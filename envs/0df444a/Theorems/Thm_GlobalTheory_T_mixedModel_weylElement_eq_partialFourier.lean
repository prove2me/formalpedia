-- Prove2me | Theorems.Thm_GlobalTheory_T_mixedModel_weylElement_eq_partialFourier
-- name    : GlobalTheory.T.mixedModel_weylElement_eq_partialFourier
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:52:37.272665+00:00
-- url     : https://prove2.me/theorems/ab998733-7ae4-4c40-b15e-5a095a10c491
-- title:
--   T: mixed Model weyl Element eq partial Fourier
-- statement:
--   The T construction uses the mixed Model weyl Element eq partial Fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelWeylElementEqPartialFourierStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelWeylElementEqPartialFourierStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourierStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mixedModel_weylElement_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by sorry
