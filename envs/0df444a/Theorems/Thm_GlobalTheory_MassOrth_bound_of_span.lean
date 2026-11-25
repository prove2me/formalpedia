-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_bound_of_span
-- name    : GlobalTheory.MassOrth.bound_of_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:17.564799+00:00
-- url     : https://prove2.me/theorems/2a83ce10-9cca-4a6e-8dc2-53e49ec59fd1
-- title:
--   Mass Orth: bound of span
-- statement:
--   The Mass Orth construction uses the bound of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L31-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem GlobalTheory.MassOrth.bound_of_span (h : V →ₗ⋆[K] V →ₗ[K] K) (T : Set V) (m : Γ)
    (hT : ∀ x ∈ T, ∀ y ∈ T, v (h x y) ≤ m) :
    ∀ x ∈ Submodule.span (biInt v) T, ∀ y ∈ Submodule.span (biInt v) T, v (h x y) ≤ m := by sorry
