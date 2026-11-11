-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_39
-- name    : GraphSimOT.Gaps.theorem_39
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:53.139962+00:00
-- url     : https://prove2.me/theorems/f4eb4038-2f19-4048-87bc-62f189d100d8
-- title:
--   Theorem 39 — additive rounding: some permutation matrix P has ζ_P ≤ ζ_Q + 36√d_n n^{−1/6}, d_n = ⌈2 log n⌉
-- statement:
--   Let $G, H$ be graphs on $[n]$, $n\ge2$ (App. E.2), and $d_n := \lceil 2\log n\rceil$ (binary logarithm). For every $Q\in\mathrm{DS}(n)$ there is a permutation matrix $P$ with
--   $$\zeta_P\ \le\ \zeta_Q + 36\sqrt{d_n}\,n^{-1/6}.$$
--
--   With $Q$ optimal this gives $\delta_\square\le\delta^{OT}_\square + 36\sqrt{d_n}n^{-1/6}$, the additive half of Theorem 11, used when $\delta^{OT}_\square$ is not too small relative to $n$.
--
--   Differences from the source:
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
--   - encoding: d_n := ⌈2 log n⌉ with log binary (p. 5) → ⌈2 * Real.logb 2 n⌉₊ (Nat.ceil), cast to ℝ; reason: 2 log₂ n ≥ 2 > 0 for n ≥ 2, so Nat.ceil is the ceiling
--   - encoding: a permutation matrix P ∈ Perm(n) → π.permMatrix ℝ for π : Equiv.Perm (Fin n); reason: Perm(n) is exactly the set of these matrices
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 36, Theorem 39

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding

namespace GraphSimOT.Gaps

/-- Theorem 39 (App. E.2.2, p. 36): let `d_n := ⌈2 log₂ n⌉`. For every `Q ∈ DS(n)` (`n ≥ 2`)
there is a permutation matrix `P` with `ζ_P ≤ ζ_Q + 36 √d_n n^{-1/6}`. -/
theorem theorem_39 {n : ℕ} (hn : 2 ≤ n) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), zeta G H (π.permMatrix ℝ) ≤
      zeta G H Q + 36 * Real.sqrt (⌈2 * Real.logb 2 n⌉₊ : ℝ) * (n : ℝ) ^ (-(1 / 6 : ℝ)) := by sorry

end GraphSimOT.Gaps
