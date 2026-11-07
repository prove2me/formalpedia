-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_10
-- name    : IterRoundDet.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:22.330012+00:00
-- url     : https://prove2.me/theorems/ab360caf-4e58-442f-8695-4331294c94d4
-- title:
--   Lemma 3.10 — positive curvature for $f-g_1$ when $m\ge 12d>0$
-- statement:
--   If a proportional pair has $m\ge 12d>0$ fractional coordinates, there is a nonzero balanced $v$ for which
--
--   $$\frac{d^2}{dt^2}(f-g_1)(a+tv,x+tw)\Big|_{t=0}>0.$$
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.10, (29), p.17

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Regularizer

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.10, (29), p.17. If a proportional pair has `m ≥ 12d > 0` fractional coordinates, there is a
nonzero balanced `v` for which `d²/dt² (f − g₁)(a + tv, x + tw)|_{t=0} > 0`. -/
theorem lemma_3_10 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c)
    {M : Matroid (Fin n)} (hM : M.E = Set.univ) {a x : Fin n → ℝ} (hax : Feasible c M a x)
    {π : Finpartition (fractional x)} (hπ : IsFacePartition M x π) (hprop : IsProportional a x π)
    (hm : 12 * d ≤ (fractional x).card) (hd : 0 < d) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ IsBalanced c a π v ∧
      0 < deriv (deriv fun t : ℝ => fMinusG1 c d (a + t • v) (x + t • extendDir a x v)) 0 := by sorry

end IterRoundDet
