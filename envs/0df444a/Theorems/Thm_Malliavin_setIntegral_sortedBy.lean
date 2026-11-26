-- Prove2me | Theorems.Thm_Malliavin_setIntegral_sortedBy
-- name    : Malliavin.setIntegral_sortedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:28.986491+00:00
-- url     : https://prove2.me/theorems/148250ee-7beb-55a5-9d68-75422be24cc1
-- title:
--   Malliavin: set Integral sorted By
-- statement:
--   Every tile `sortedBy σ` carries the same integral of a symmetric function as the simplex.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L260-L271
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L260-L271

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Malliavin.setIntegral_sortedBy {n : ℕ} {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    (σ : Equiv.Perm (Fin n)) :
    ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) =
      ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by sorry
