-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_not_tempered_diag_spEig
-- name    : GlobalTheory.WeilDeligne.not_tempered_diag_spEig
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:31.33627+00:00
-- url     : https://prove2.me/theorems/802148f0-b6eb-4f69-8109-01210ee121de
-- title:
--   Weil Deligne: not tempered diag sp Eig
-- statement:
--   The Weil Deligne construction uses the not tempered diag sp Eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L659-L666
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L659-L666

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

theorem GlobalTheory.WeilDeligne.not_tempered_diag_spEig : ¬ (WD.mk (WDRep.diag h (WDRep.spEig w 2))).tempered := by sorry
