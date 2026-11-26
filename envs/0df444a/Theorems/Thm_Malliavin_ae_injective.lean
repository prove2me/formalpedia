-- Prove2me | Theorems.Thm_Malliavin_ae_injective
-- name    : Malliavin.ae_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:32.306829+00:00
-- url     : https://prove2.me/theorems/3c36aebb-75ff-4c94-bdd5-b5b8b8b229d5
-- title:
--   Malliavin: ae injective
-- statement:
--   The Malliavin construction uses the ae injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L248-L250
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L248-L250

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

theorem Malliavin.ae_injective [NullSingletonClass μ] (n : ℕ) :
    ∀ᵐ t ∂(Measure.pi fun _ : Fin n => μ), Function.Injective t := by sorry
