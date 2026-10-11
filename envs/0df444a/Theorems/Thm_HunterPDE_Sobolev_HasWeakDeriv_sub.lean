-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
-- name    : HunterPDE.Sobolev.HasWeakDeriv.sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:40:29.409656+00:00
-- url     : https://prove2.me/theorems/55eca9db-d42e-49ad-a078-276a03bd7540
-- title:
--   Subtraction of weak multi-index derivatives
-- statement:
--   If u is a weak multi-index derivative of f and v is the corresponding weak derivative of g on a domain, then u minus v is the weak derivative of f minus g. All four functions are locally integrable on the domain. No Lp or smoothness assumption on f and g is required.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 47–48, Definitions 3.1–3.2 and uniqueness discussion; subtraction follows by linearity of the defining integrals.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.HasWeakDeriv.sub {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {α : Fin n → ℕ} {f g u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasWeakDeriv Ω α f u) (hv : HasWeakDeriv Ω α g v) :
    HasWeakDeriv Ω α (f - g) (u - v) := by sorry
