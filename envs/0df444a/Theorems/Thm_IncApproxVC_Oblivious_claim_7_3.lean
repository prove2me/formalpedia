-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_claim_7_3
-- name    : IncApproxVC.Oblivious.claim_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:41.75468+00:00
-- url     : https://prove2.me/theorems/2f500033-f7d4-496a-ac81-618b91a0f8c6
-- title:
--   Claim 7.3 — maintaining whether $G$ is strongly connected under edge insertions in $\tilde O(m)$ total time
-- statement:
--   A graph $G$ on $n$ vertices can be maintained under edge insertions supplied by a randomness-adaptive adversary, reporting after every insertion whether $G$ is strongly connected, in total time $\tilde O(m)$, where $m$ is the number of edges after all insertions.
--
--   Formally: there are $C>0$ and a coin-free program such that for every valid incremental instance (initial graph as adjacency lists, header $[0,n]$), every run halts, the total work is at most
--   $$C\,m\,(1+\log m)^{C}+C,$$
--   and after the $i$-th insertion ($i\ge 1$) the output in real cell $-1$ is $1$ if $G_i$ is strongly connected and $0$ if not. Algorithm 3 uses it to output $0$ until the graph becomes strongly connected.
--
--   Differences from the source:
--   - reading: a randomized (or deterministic) incremental algorithm / data structure; no machine is named → one admissible program of the published randomized exact real RAM PNormReg (coin-free for a deterministic algorithm), operations fed online by runOps with the layout of IncApproxVC.Oblivious.Online; reason: the paper names no machine; this is the unit-cost exact real RAM of the published PNormReg_Machine, with free input loading so that local time bounds are meaningful
--   - reading: Õ(m) time → ≤ C·m·(1 + log m)^C + C with one universal constant C; reason: the polylogarithmic factor in m (logs of n are not needed: m < n − 1 already decides the answer)
--   - reading: a randomness-adaptive adversary → a coin-free program and every valid insertion sequence; reason: the proof is deterministic (two reachability structures, Claim 7.2); against a deterministic program an adaptive adversary is any sequence
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 24, Claim 7.3

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity
import Definitions.Def_IncApproxVC_Oblivious_Online

namespace IncApproxVC.Oblivious

/-- **Claim 7.3** (handling `κ(G) = 0`), p. 24. There are `C > 0` and one coin-free admissible
program `P` such that for every `n` and every valid incremental instance on `Fin n`, fed online with
the header `[0, n]` (initial graph as adjacency lists, then one insertion at a time; any insertion
sequence, as for a randomness-adaptive adversary against a deterministic algorithm): every run
halts, the total work is at most `C m (1 + log m)^C + C` with `m` the number of edges after all
insertions (`Õ(m)`), and after the `i`-th insertion (`i ≥ 1`) the output (real cell `−1`) is `1` if
`G_i` is strongly connected and `0` if it is not. -/
theorem claim_7_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : PNormReg.Program, PNormReg.Admissible P ∧ CoinFree P ∧
      ∀ n : ℕ, ∀ I : IncInstance n, I.Valid →
        let T : ℝ := C * (I.finalEdgeCount : ℝ) * (1 + Real.log I.finalEdgeCount) ^ C + C
        let mops := insertionOps [0, (n : ℤ)] [] I
        (∀ i, i ≤ I.ins.length → (runOps P noCoins ⌊T⌋₊ mops (i + 1)).halted = true) ∧
        ((runOps P noCoins ⌊T⌋₊ mops (I.ins.length + 1)).work : ℝ) ≤ T ∧
        ∀ i, 1 ≤ i → i ≤ I.ins.length →
          ((runOps P noCoins ⌊T⌋₊ mops (i + 1)).core.mem (-1) = 1 ∧
              (I.graphAfter i).IsStronglyConnected) ∨
            ((runOps P noCoins ⌊T⌋₊ mops (i + 1)).core.mem (-1) = 0 ∧
              ¬ (I.graphAfter i).IsStronglyConnected) := by sorry

end IncApproxVC.Oblivious
