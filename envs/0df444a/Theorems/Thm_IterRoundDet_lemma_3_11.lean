-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_11
-- name    : IterRoundDet.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:42.278412+00:00
-- url     : https://prove2.me/theorems/a0d6370a-ab11-41e0-9264-d5440f207207
-- title:
--   Lemma 3.11 — positive curvature for $f-g_2$ at a proportional pair with a fractional coordinate
-- statement:
--   If $x$ has a fractional coordinate at a proportional pair, there is a nonzero balanced $v$ for which
--
--   $$\frac{d^2}{dt^2}(f-g_2)(a+tv,x+tw)\Big|_{t=0}=3\sum_{i\in A}\frac{v_i^2}{a_i(1-a_i)}-v^\top C^\dagger v>0.$$
--
--   This is where real stability is used, through $C_{ij}\le 0$.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.11, p.18

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Regularizer
import Definitions.Def_IterRoundDet_Covariance

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.11, p.18. If `x` has a fractional coordinate at a proportional pair, there is a nonzero
balanced `v` for which `d²/dt² (f − g₂)(a + tv, x + tw)|_{t=0} = 3 ∑_{i∈A} v_i²/(a_i(1 − a_i)) − v⊤C†v > 0`. -/
theorem lemma_3_11 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c)
    {M : Matroid (Fin n)} (hM : M.E = Set.univ) {a x : Fin n → ℝ} (hax : Feasible c M a x)
    {π : Finpartition (fractional x)} (hπ : IsFacePartition M x π) (hprop : IsProportional a x π)
    {μ : Finset (Fin n) → ℝ} (hμ : IsMaxEnt c a μ) (hA : (fractional x).Nonempty) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ IsBalanced c a π v ∧
      deriv (deriv fun t : ℝ => fMinusG2 c (a + t • v) (x + t • extendDir a x v)) 0 =
        3 * ∑ i ∈ fractional x, v i ^ 2 / (a i * (1 - a i)) - pinvForm (covMat μ a) v ∧
      0 < 3 * ∑ i ∈ fractional x, v i ^ 2 / (a i * (1 - a i)) - pinvForm (covMat μ a) v := by sorry

end IterRoundDet
