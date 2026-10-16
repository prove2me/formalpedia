-- Prove2me | Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
-- name    : HunterPDE.Shared.HasWeakDeriv.ae_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T17:46:58.491983+00:00
-- url     : https://prove2.me/theorems/3beb368d-c86e-4d3e-bdd8-2c1293a8e66d
-- title:
--   Uniqueness almost everywhere of shared multi-index weak derivatives
-- statement:
--   Let $\Omega$ be open in Euclidean space. If $u$ and $v$ are locally integrable weak derivatives of the same function $f$ with the same multi-index, then $u=v$ almost everywhere on $\Omega$. This uses the shared weak derivative definition, whose test derivative is the ordered coordinate list. There is no Sobolev exponent hypothesis.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 2014-06-18, §3.1, pp. 47–48, uniqueness of weak derivatives following Definition 3.1. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . The proof uses Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.HasWeakDeriv.ae_eq {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {α : Fin n → ℕ}
    {f u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasWeakDeriv Ω α f u) (hv : HasWeakDeriv Ω α f v) :
    u =ᵐ[volume.restrict Ω] v := by sorry
