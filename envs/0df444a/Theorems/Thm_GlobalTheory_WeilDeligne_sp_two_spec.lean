-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_sp_two_spec
-- name    : GlobalTheory.WeilDeligne.sp_two_spec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:57:30.499698+00:00
-- url     : https://prove2.me/theorems/8b822515-b110-5360-b289-3108a1378ceb
-- title:
--   Weil Deligne: sp two spec
-- statement:
--   The Weil Deligne construction uses the sp two spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L654-L657
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L654-L657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
variable (h : IsPlaceOver A w)

theorem GlobalTheory.WeilDeligne.sp_two_spec : (WD.lpSp h 2).lpDim = 2 ∧ (WD.lpSp h 2).tempered ∧ ¬ (WD.lpSp h 2).mono0 ∧
    ¬ (WD.lpSp h 2).unr := by sorry
