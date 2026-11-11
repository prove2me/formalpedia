-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_theorem_1_1
-- name    : IncApproxVC.Oblivious.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:48.565632+00:00
-- url     : https://prove2.me/theorems/0d5ab9bc-0b5e-42f9-83af-f93dba9e6289
-- title:
--   Theorem 1.1 — incremental $(1+\varepsilon)$-approximate vertex connectivity, oblivious adversary, in $O(\varepsilon^{-3}m^{1+o(1)})$ total time ($O(\varepsilon^{-2}m^{1+o(1)})$ while $\kappa<0.99n$)
-- statement:
--   There is a randomized incremental algorithm for approximate vertex connectivity with an oblivious adversary that outputs a $(1+\varepsilon)$-approximation of the vertex connectivity after every edge insertion with high probability. Its total running time is $O(\varepsilon^{-3}m^{1+o(1)})$, and $O(\varepsilon^{-2}m^{1+o(1)})$ if the vertex connectivity stays below $0.99n$.
--
--   Precisely: there are universal constants $C>0$ and $c\ge 1$, a function $g:\mathbb N\to\mathbb R$ with $g(m)\to 0$, and one admissible program $P$ of the randomized real RAM, such that the following holds. Take any $n\ge 1$, any $\varepsilon\in(0,1]$, any simple directed initial graph $G_0$ on $n$ vertices and any insertions $e_1,\dots,e_\ell$ keeping the graph simple, all fixed before the coins. Let $G_i$ be the graph after $i$ insertions and $m=|E(G_0)|+\ell$. Feed the instance to $P$ online, initialization first and then one insertion at a time, with output $\mathrm{out}_i$ after each. Then:
--   - (a) on every coin tape every run halts and the total work is at most $C\varepsilon^{-3}m^{1+g(m)}+C$;
--   - (b) if $\kappa(G_i)<0.99n$ for every $i$, the total work is at most $C\varepsilon^{-2}m^{1+g(m)}+C$ on every coin tape;
--   - (c) the probability that some output violates
--   $$\kappa(G_i)\ \le\ \mathrm{out}_i\ \le\ (1+\varepsilon)\,\kappa(G_i)\qquad(i=0,\dots,\ell)$$
--   is at most $n^{-c}$.
--
--   Here $\kappa$ is the vertex connectivity: the minimum size of a set whose deletion leaves a graph that is not strongly connected, or of size $n-1$. The theorem is the paper's headline result, restated as Theorem 7.10.
--
--   **Formalization Note.** Header $[0,n]$ and the real word $\varepsilon$; $\mathrm{out}_i$ is real cell $-1$ after operation $i$. The probability is the outer measure, under the fair-coin measure `PNormReg.coinTape`, of the set of tapes on which some output is wrong or some run did not halt within the fuel $\lfloor C\varepsilon^{-3}m^{1+g(m)}+C\rfloor$.
--
--   Differences from the source:
--   - reading: a randomized (or deterministic) incremental algorithm / data structure; no machine is named → one admissible program of the published randomized exact real RAM PNormReg (coin-free for a deterministic algorithm), operations fed online by runOps with the layout of IncApproxVC.Oblivious.Online; reason: the paper names no machine; this is the unit-cost exact real RAM of the published PNormReg_Machine, with free input loading so that local time bounds are meaningful
--   - reading: total running time O(ε⁻³m^{1+o(1)}); O(ε⁻²m^{1+o(1)}) if κ stays below 0.99n → total work ≤ C·ε⁻³·m^{1+g(m)} + C, resp. ≤ C·ε⁻²·m^{1+g(m)} + C when κ(G_i) < 0.99n for all i; one universal C and one g → 0 for both; reason: O and o(1) as explicit universal constants (the additive C covers m ≤ 1); never dependent on n, ε or the instance
--   - reading: total running time (no probability qualifier) → on every coin tape; reason: the printed time clauses are unconditional; the proof bounds time only on the good event (INSIGHTS I2), which is a finding, not a licence to weaken
--   - reading: with high probability → probability ≤ n^{−c} with one universal c ≥ 1 fixed before the instance; the outer measure of the failure set, a run that did not halt counting as a failure; reason: 'w.h.p.' is defined on p. 2 as probability ≥ 1 − n^{−c} for some constant c ≥ 1
--   - reading: outputs a (1+ε)-approximation of the vertex connectivity → κ(G_i) ≤ out_i ≤ (1+ε)κ(G_i); reason: the over-estimating direction of Algorithm 3 and Lemma 7.8 (it outputs values ≥ κ, and n once κ is large)
--   - reading: after every edge insertion; m edge insertions → an output after initialization (i = 0) and after each of the ℓ insertions; m = |E(G₀)| + ℓ; reason: Theorem 7.10: m is the number of edges after all insertions; Algorithm 3 reports from the start
--   - encoding: graphs, ε → simple directed graphs on Fin n with n ≥ 1 (IncInstance.Valid); ε ∈ (0, 1] given as a real word; reason: standing assumption p. 3; Algorithm 3's input domain, p. 24 (for ε > 1 the bound cannot hold)
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 1, Theorem 1.1 (formal restatement Theorem 7.10, p. 28; 'with high probability' and logarithms, p. 2; Algorithm 3's input ε ∈ (0, 1], p. 24)

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity
import Definitions.Def_IncApproxVC_Oblivious_Online

open Filter Topology

namespace IncApproxVC.Oblivious

/-- **Theorem 1.1** (incremental `(1 + ε)`-approximate vertex connectivity, oblivious adversary),
p. 1; restated as Theorem 7.10, p. 28. There are universal constants `C > 0` and `c ≥ 1`, a function
`g : ℕ → ℝ` with `g(m) → 0` and one admissible program `P` of the randomized real RAM such that for
every `n ≥ 1`, every `ε ∈ (0, 1]` and every valid incremental instance on `Fin n` (a simple initial
graph `G₀` given as adjacency lists and insertions `e₁, …, e_ℓ` keeping it simple, fixed before the
coin tape), fed online with the header `[0, n]` and the real word `ε`, with `m = |E(G₀)| + ℓ`:
* (a) on every coin tape every run halts and the total work is at most `C ε⁻³ m^{1+g(m)} + C`;
* (b) if `κ(G_i) < 0.99 n` for every `i = 0, …, ℓ`, the total work is at most
  `C ε⁻² m^{1+g(m)} + C` on every coin tape;
* (c) the coin-tape probability (outer measure) that some output `out_i` (real cell `−1` after the
  initialization, `i = 0`, or after the `i`-th insertion) fails `κ(G_i) ≤ out_i ≤ (1 + ε) κ(G_i)`,
  or that some run did not halt, is at most `n^{−c}`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 1 ≤ c ∧ ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∃ P : PNormReg.Program, PNormReg.Admissible P ∧
        ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ I : IncInstance n, I.Valid →
          let m : ℕ := I.finalEdgeCount
          let T : ℝ := C * ε⁻¹ ^ 3 * (m : ℝ) ^ (1 + g m) + C
          let mops := insertionOps [0, (n : ℤ)] [ε] I
          (∀ ω : ℕ → Bool,
              (∀ i, i ≤ I.ins.length → (runOps P ω ⌊T⌋₊ mops (i + 1)).halted = true) ∧
              ((runOps P ω ⌊T⌋₊ mops (I.ins.length + 1)).work : ℝ) ≤ T) ∧
          ((∀ i, i ≤ I.ins.length → ((I.graphAfter i).kappa : ℝ) < 0.99 * n) →
            ∀ ω : ℕ → Bool,
              ((runOps P ω ⌊T⌋₊ mops (I.ins.length + 1)).work : ℝ) ≤
                C * ε⁻¹ ^ 2 * (m : ℝ) ^ (1 + g m) + C) ∧
          PNormReg.coinTape {ω | ∃ i, i ≤ I.ins.length ∧
              ¬ ((runOps P ω ⌊T⌋₊ mops (i + 1)).halted = true ∧
                ((I.graphAfter i).kappa : ℝ) ≤ answer P ω ⌊T⌋₊ mops i ∧
                answer P ω ⌊T⌋₊ mops i ≤ (1 + ε) * ((I.graphAfter i).kappa : ℝ))} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end IncApproxVC.Oblivious
