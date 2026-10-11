-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq
-- name    : HunterPDE.Sobolev.HasWeakDeriv.ae_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:37:51.94977+00:00
-- url     : https://prove2.me/theorems/6027379e-bb59-4dc6-ac2d-5037e2458012
-- title:
--   Almost-everywhere uniqueness of a weak multi-index derivative
-- statement:
--   On an open subset of Euclidean space, two locally integrable functions representing the same weak multi-index derivative of a function agree almost everywhere on that domain. This holds for every multi-index, including order zero, without an Lp hypothesis.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 47–48, Definitions 3.1–3.2 and uniqueness discussion; subtraction follows by linearity of the defining integrals.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.HasWeakDeriv.ae_eq {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {α : Fin n → ℕ}
    {f u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasWeakDeriv Ω α f u) (hv : HasWeakDeriv Ω α f v) :
    u =ᵐ[volume.restrict Ω] v := by sorry
