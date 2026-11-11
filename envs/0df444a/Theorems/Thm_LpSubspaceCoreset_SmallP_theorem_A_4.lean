-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_theorem_A_4
-- name    : LpSubspaceCoreset.SmallP.theorem_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:48:11.559679+00:00
-- url     : https://prove2.me/theorems/9a7b1fb9-d1c1-4f39-848f-ed41c8dbfe72
-- title:
--   Theorem A.4 — row-augmented subspace entropy
-- statement:
--   Fix $1\le p\le2$. There is $C_p$ such that the following holds. Let $H$ be a finite-dimensional real Hilbert space, $q$ a finitely supported probability law, $u_i\in H$ unit vectors and $b_i\in H$ arbitrary fixed vectors (zero allowed). For every $k$-dimensional subspace $F\subseteq H$ define
--   $$f_F(i)=\operatorname{dist}\big(u_i,F+\operatorname{span}\{b_i\}\big)^p .$$
--   For $0<\delta\le1$ and $k\ge1$,
--   $$\log N(\delta,\{f_F\},L_2(q))\le C_p\,k\,\delta^{-2}\big(1+\log(k+2)+\log(1/\delta)\big)^{C_p},\qquad(A.10)$$
--   independently of the number of rows and of the dimension of $H$.
--
--   It controls the coordinate of the residual orthogonal to both the query subspace and the low-rank row.
--
--   Differences from the source:
--   - reading: C_p k δ^{-2} polylog(k + 2, 1/δ) → C·k·δ^{-2}·(1 + log(k + 2) + log(1/δ))^C, one C = C_p; reason: polylog(x, y) = C(1 + log x + log y)^C
--   - encoding: log N(δ, {f_F}, L2(q)) ≤ X → some finite internal δ-cover 𝒩 has log |𝒩| ≤ X; reason: equivalent; avoids a junk value
--   - encoding: q a finitely supported probability law → q a probability law on a finite index type; reason: only the support matters
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 40, Theorem A.4

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Process

namespace LpSubspaceCoreset.SmallP

/-- **Theorem A.4** (Row-augmented subspace entropy), p. 40.

Fix `1 ≤ p ≤ 2`; there is `C_p` such that the following holds. Let `H` be a finite-dimensional
real Hilbert space, `q` a finitely supported probability law (on a finite index set), `u_i ∈ H`
unit vectors and `b_i ∈ H` arbitrary (zero allowed). For every `k`-dimensional subspace `F ⊆ H`
let `f_F(i) = dist(u_i, F + span{b_i})^p`. For `k ≥ 1` and `0 < δ ≤ 1` some internal `δ`-cover
`𝒩` of `{f_F}` in `L2(q)` has `log |𝒩| ≤ C_p k δ^{−2} (1 + log(k + 2) + log(1/δ))^{C_p}`
(`C_p k δ^{−2} polylog(k + 2, 1/δ)`), independently of the number of rows and of `dim H`. -/
theorem theorem_A_4 :
    ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
      (ι : Type) [Fintype ι] (q : ι → ℝ), IsProbLaw q →
    ∀ (u b : ι → H), (∀ i, ‖u i‖ = 1) →
    ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ 𝒩 : Finset (ι → ℝ),
        IsCover q δ {f | ∃ F : Submodule ℝ H, Module.finrank ℝ F = k ∧
          f = fun i => Metric.infDist (u i) ↑(F ⊔ Submodule.span ℝ {b i}) ^ p} 𝒩 ∧
        Real.log 𝒩.card ≤ C * k / δ ^ 2 * (1 + Real.log (k + 2) + Real.log (1 / δ)) ^ C := by sorry

end LpSubspaceCoreset.SmallP
