-- Prove2me | Theorems.Thm_GlobalTheory_PlaceOver_isOpen_valuation_lt_one
-- name    : GlobalTheory.PlaceOver.isOpen_valuation_lt_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:44:43.591659+00:00
-- url     : https://prove2.me/theorems/a66f813b-f8d1-4c81-b2fc-1c25820b8ed3
-- title:
--   Place Over: is Open valuation lt one
-- statement:
--   The Place Over construction uses the is Open valuation lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapEqOfContinuousAdicCompletionIso.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapEqOfContinuousAdicCompletionIso.lean#L12-L15

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapEqOfContinuousAdicCompletionIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.PlaceOver
open Filter Topology

theorem GlobalTheory.PlaceOver.isOpen_valuation_lt_one {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) :
    IsOpen {z : P.adicCompletion F | Valued.v z < 1} := by sorry
