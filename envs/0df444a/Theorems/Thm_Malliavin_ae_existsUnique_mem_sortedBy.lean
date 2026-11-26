-- Prove2me | Theorems.Thm_Malliavin_ae_existsUnique_mem_sortedBy
-- name    : Malliavin.ae_existsUnique_mem_sortedBy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:56:50.69449+00:00
-- url     : https://prove2.me/theorems/f19a93e3-bdcf-59a4-a6b6-00d35c0b5358
-- title:
--   Malliavin: ae exists Unique mem sorted By
-- statement:
--   Almost every tuple is sorted by exactly one permutation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L253-L257
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L253-L257

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

theorem Malliavin.ae_existsUnique_mem_sortedBy [NullSingletonClass μ] (n : ℕ) :
    ∀ᵐ t ∂(Measure.pi fun _ : Fin n => μ), ∃! σ : Equiv.Perm (Fin n), t ∈ sortedBy T n σ := by sorry
