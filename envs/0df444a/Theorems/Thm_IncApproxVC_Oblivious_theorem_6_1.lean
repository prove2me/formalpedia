-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_theorem_6_1
-- name    : IncApproxVC.Oblivious.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:25.640321+00:00
-- url     : https://prove2.me/theorems/5045a9b9-f43d-49be-b8f0-1b94697bc8bf
-- title:
--   Theorem 6.1 — deterministic incremental local edge cut: YES/NO after every insertion in $O((\varepsilon^{-1}\nu^{1+o(1)}+\ell^{1+o(1)})\operatorname{poly}\log n)$ total time
-- statement:
--   There is a deterministic incremental local edge cut algorithm. Its input is an initial simple graph $G=(V,E)$ with $m$ edges, given as adjacency lists, a source $s$, integers $k\in[1,n]$ and $\nu\in[1,n^2]$, and a fraction $\varepsilon=a/b\in(0,1)$ with $a,b\in[1,\operatorname{poly}(n)]$, such that $\nu<\tfrac12\varepsilon m$. It processes $\ell$ edge insertions chosen by a randomness-adaptive adversary in total time
--   $$O\Big(\big(\varepsilon^{-1}\nu^{1+o(1)}+\ell^{1+o(1)}\big)\operatorname{poly}\log n\Big).$$
--   After initialization and after every insertion it outputs
--   - YES, meaning there is an edge cut $(S,T)$ of size $\le(1+\varepsilon)k$ with $s\in S$ and $\mathrm{vol}^+(S)\le 2\nu/\varepsilon$; on request it outputs such a set $S$ in $O(\varepsilon^{-1}\nu^{1+o(1)}\operatorname{poly}\log n)$ time per query; or
--   - NO, meaning there is no edge cut $(S,T)$ of size $\le k$ with $s\in S$ and $\mathrm{vol}^+(S)\le\nu$.
--
--   Formally: for every exponent $d$ ($a,b\le n^d$) there are $C>0$, $g\to 0$ and a coin-free program such that for every operation sequence (insertions keeping the graph simple, and queries) every run halts; initialization and insertions take total work at most $C(\varepsilon^{-1}\nu^{1+g(\nu)}+\ell^{1+g(\ell)})(1+\log n)^C+C$; each query takes at most $C\varepsilon^{-1}\nu^{1+g(\nu)}(1+\log n)^C+C$; the outputs are correct; and a query made while the latest output is YES writes such an $S$.
--
--   Differences from the source:
--   - reading: a randomized (or deterministic) incremental algorithm / data structure; no machine is named → one admissible program of the published randomized exact real RAM PNormReg (coin-free for a deterministic algorithm), operations fed online by runOps with the layout of IncApproxVC.Oblivious.Online; reason: the paper names no machine; this is the unit-cost exact real RAM of the published PNormReg_Machine, with free input loading so that local time bounds are meaningful
--   - reading: O((ε⁻¹ν^{1+o(1)} + ℓ^{1+o(1)}) poly log n) total, O(ε⁻¹ν^{1+o(1)} poly log n) per query; numerator and denominator in [1, poly(n)] → ∀ d ∃ C g P: a, b ≤ n^d; total work of initialization and insertions ≤ C(ε⁻¹ν^{1+g(ν)} + ℓ^{1+g(ℓ)})(1+log n)^C + C; each query ≤ C ε⁻¹ν^{1+g(ν)}(1+log n)^C + C; reason: explicit universal constants for O, o(1), poly and poly log
--   - reading: a sequence of ℓ edge insertions provided by a randomness-adaptive adversary; Optionally, the algorithm can output a corresponding set S → every operation sequence of insertions (keeping the graph simple) and queries; a query made while the latest output is YES writes such a set S (SetsWritten); reason: a deterministic program against every sequence covers every adaptive adversary; the optional output is a clause of the statement
--   - encoding: ν < ½εm with m the edge count of the input graph → ν < 1/2 · (a/b) · |E(G₀)|; reason: m of the initial graph (the condition only weakens as edges are inserted)
--   - reading: an initial graph G = (V, E) represented as an adjacency list → G₀ loaded for free as adjacency arrays: block offsets, then per vertex deg⁺ and the out-neighbours, deg⁻ and the in-neighbours (the adjacency lists of G and of ←G); reason: the representation of a directed graph that Algorithm 3 needs, since it runs IncLocalVC on both G and ←G (p. 24, lines 3–7); the in-lists add no instance and loading is free so the local time bounds are meaningful
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 19, Theorem 6.1

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_Cuts
import Definitions.Def_IncApproxVC_Oblivious_Online

open Filter Topology Classical

namespace IncApproxVC.Oblivious

/-- **Theorem 6.1** (deterministic incremental local edge cut), p. 19. For every exponent `d` (the
`poly(n)` bound on the numerator and denominator of `ε`) there are `C > 0`, a function `g → 0` and
one coin-free admissible program `P` such that the following holds for every `n`, every initial
graph `G₀` on `Fin n` given as adjacency lists, every source `s`, all integers `k ∈ [1, n]`,
`ν ∈ [1, n²]`, `ε = a/b ∈ (0, 1)` with `a, b ∈ [1, n^d]` and `ν < ½ ε m` (`m = |E(G₀)|`), and every
sequence of operations (edge insertions keeping the graph simple, and set-output queries; any
sequence, as for a randomness-adaptive adversary against a deterministic algorithm), fed online with
the header `[0, n, s, k, ν, a, b]`:
* every run halts, and the initialization and the `ℓ` insertions take total work at most
  `C (ε⁻¹ ν^{1+g(ν)} + ℓ^{1+g(ℓ)}) (1 + log n)^C + C`;
* after initialization and after every insertion the output (real cell `−1`) is `1` (YES) and the
  current graph has an edge cut `(S, V \ S)` with `s ∈ S`, `|∂⁺(S)| ≤ (1 + ε)k` and
  `vol⁺(S) ≤ 2ν/ε`, or it is `0` (NO) and the current graph has no edge cut `(S, V \ S)` with
  `s ∈ S`, `|∂⁺(S)| ≤ k` and `vol⁺(S) ≤ ν`;
* every query takes work at most `C ε⁻¹ ν^{1+g(ν)} (1 + log n)^C + C`, and a query made while the
  latest output is YES writes such a set `S` (`SetsWritten`, one set). -/
theorem theorem_6_1 :
    ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∃ P : PNormReg.Program, PNormReg.Admissible P ∧ CoinFree P ∧
      ∀ n : ℕ, ∀ G₀ : Digraph (Fin n), ∀ s : Fin n, ∀ k ν a b : ℕ,
        1 ≤ k → k ≤ n → 1 ≤ ν → ν ≤ n ^ 2 → 1 ≤ a → a ≤ n ^ d → 1 ≤ b → b ≤ n ^ d → a < b →
        (ν : ℝ) < 1 / 2 * ((a : ℝ) / b) * (G₀.numEdges : ℝ) →
        ∀ ops : List (LocalOp n), (LocalOp.toInstance G₀ ops).Valid →
          let ε : ℝ := (a : ℝ) / b
          let ℓ : ℕ := LocalOp.numInsertions ops
          let Ttot : ℝ := C * (ε⁻¹ * (ν : ℝ) ^ (1 + g ν) + (ℓ : ℝ) ^ (1 + g ℓ)) *
            (1 + Real.log n) ^ C + C
          let Tq : ℝ := C * (ε⁻¹ * (ν : ℝ) ^ (1 + g ν)) * (1 + Real.log n) ^ C + C
          let mops := localOps [0, (n : ℤ), vword s, (k : ℤ), (ν : ℤ), (a : ℤ), (b : ℤ)] G₀ ops
          let fuel : ℕ := ⌊Ttot + Tq⌋₊
          let IsOutput : ℕ → Prop := fun j => j = 0 ∨ ∃ u v, ops[j - 1]? = some (LocalOp.insert u v)
          (∀ j, j ≤ ops.length → (runOps P noCoins fuel mops (j + 1)).halted = true) ∧
          ((∑ j ∈ (Finset.range (ops.length + 1)).filter IsOutput,
              opWork P noCoins fuel mops j : ℕ) : ℝ) ≤ Ttot ∧
          (∀ j, ops[j]? = some LocalOp.query → (opWork P noCoins fuel mops (j + 1) : ℝ) ≤ Tq) ∧
          (∀ j, j ≤ ops.length → IsOutput j →
            ((runOps P noCoins fuel mops (j + 1)).core.mem (-1) = 1 ∧
                ∃ S : Finset (Fin n), s ∈ S ∧ Digraph.IsEdgeCut S Sᶜ ∧
                  (((LocalOp.graphAfterOps G₀ ops j).outBoundary S).card : ℝ) ≤ (1 + ε) * k ∧
                  ((LocalOp.graphAfterOps G₀ ops j).vol S : ℝ) ≤ 2 * ν / ε) ∨
              ((runOps P noCoins fuel mops (j + 1)).core.mem (-1) = 0 ∧
                ¬ ∃ S : Finset (Fin n), s ∈ S ∧ Digraph.IsEdgeCut S Sᶜ ∧
                  ((LocalOp.graphAfterOps G₀ ops j).outBoundary S).card ≤ k ∧
                  ((LocalOp.graphAfterOps G₀ ops j).vol S : ℝ) ≤ ν)) ∧
          (∀ j, ops[j]? = some LocalOp.query →
            (∃ j', j' ≤ j ∧ IsOutput j' ∧
              (∀ j'', j' < j'' → j'' ≤ j → ops[j'' - 1]? = some LocalOp.query) ∧
              (runOps P noCoins fuel mops (j' + 1)).core.mem (-1) = 1) →
            ∃ S : Finset (Fin n), SetsWritten (runOps P noCoins fuel mops (j + 2)) 1 ![S] ∧
              s ∈ S ∧ Digraph.IsEdgeCut S Sᶜ ∧
              (((LocalOp.graphAfterOps G₀ ops (j + 1)).outBoundary S).card : ℝ) ≤ (1 + ε) * k ∧
              ((LocalOp.graphAfterOps G₀ ops (j + 1)).vol S : ℝ) ≤ 2 * ν / ε) := by sorry

end IncApproxVC.Oblivious
