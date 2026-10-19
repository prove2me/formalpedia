-- Prove2me | Theorems.Thm_HunterPDE_Compactness_weakDeriv_eLpNorm_le_sobolevNorm
-- name    : HunterPDE.Compactness.weakDeriv_eLpNorm_le_sobolevNorm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:05:41.590698+00:00
-- url     : https://prove2.me/theorems/3fefc0c1-e53c-4b2b-ab94-db3e21ce74be
-- title:
--   Each weak derivative is bounded by the Sobolev norm
-- statement:
--   Let $\Omega\subset\mathbb R^n$ be open, $1\le p<\infty$, and $|\alpha|\le k$. Whenever $g$ is a weak $\alpha$ derivative of $f$,
--   $$\|g\|_{L^p(\Omega)}\le\|f\|_{W^{k,p}(\Omega)}.$$
--   The right side is the extended-valued norm built from chosen weak derivative representatives. Weak uniqueness makes the bound independent of the representative. No finiteness or Sobolev membership is required for this extended-valued inequality.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorems 3.42 and 3.44, printed pp. 72–73. Auxiliary ingredient for the normal Green identity, not an explicit numbered theorem in the source.

import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory HunterPDE.Compactness HunterPDE.Shared
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.weakDeriv_eLpNorm_le_sobolevNorm {n k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (α : Fin n → ℕ) (hα : α ∈ multiIndicesLe n k)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : HasWeakDeriv Ω α f g) :
    eLpNorm g p (volume.restrict Ω) ≤ sobolevNorm k p Ω f := by sorry
