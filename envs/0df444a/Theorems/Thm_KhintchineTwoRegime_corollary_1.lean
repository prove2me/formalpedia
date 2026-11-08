-- Prove2me | Theorems.Thm_KhintchineTwoRegime_corollary_1
-- name    : KhintchineTwoRegime.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:10.249415+00:00
-- url     : https://prove2.me/theorems/a54d3149-3cd3-4e2d-b1b9-380750ba1ea5
-- title:
--   Corollary 1 — scalar separation $K(v)\ge7423/10000$ when $v_{(1)}+v_{(2)}\le1$
-- statement:
--   Let $v\in\mathbb R^n$ be a unit vector and let $v_{(1)}\ge v_{(2)}$ be its two largest absolute coordinates (adjoining a zero coordinate if necessary). If $v_{(1)}+v_{(2)}\le1$, then
--   $$
--   K_n(v)\ \ge\ k_0=\frac{7423}{10000}.
--   $$
--   The corollary separates vectors far from the two-coordinate extremizers from the classical value $1/\sqrt2\approx0.7071$; it drives the localization Lemma 6, and it is also the coefficient estimate behind the paper's Fourier-weight bound $W^{\le1}[f]\ge k_0^2$.
--
--   Differences from the source:
--   - encoding: v₍₁₎ + v₍₂₎ ≤ 1 for the two largest absolute coordinates (adjoining a zero coordinate if necessary) → |v i| + |v j| ≤ 1 for all i ≠ j; reason: for n ≥ 2 the maximum of |v_i| + |v_j| over i ≠ j is v₍₁₎ + v₍₂₎; for n = 1 both hypotheses hold (v₍₁₎ = 1, v₍₂₎ = 0); same instances
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Corollary 1, p.6

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime

/-- Corollary 1 (Scalar separation) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), p.6): let `v` be a unit vector and `v₍₁₎ ≥ v₍₂₎`
its two largest absolute coordinates (adjoining a zero coordinate if necessary); if
`v₍₁₎ + v₍₂₎ ≤ 1`, then `K(v) ≥ k₀ = 7423/10000`.

**Formalization Note** "`v₍₁₎ + v₍₂₎ ≤ 1`" is written `|vᵢ| + |vⱼ| ≤ 1` for all `i ≠ j`:
for `n ≥ 2` the largest such sum is `v₍₁₎ + v₍₂₎`, and for `n = 1` both conditions hold
(`v₍₁₎ = 1`, `v₍₂₎ = 0`). -/
theorem corollary_1 (n : ℕ) (v : Fin n → ℝ) (hv : l2Norm v = 1)
    (htop : ∀ i j : Fin n, i ≠ j → |v i| + |v j| ≤ 1) :
    (7423 : ℝ) / 10000 ≤ K n v := by sorry

end KhintchineTwoRegime
