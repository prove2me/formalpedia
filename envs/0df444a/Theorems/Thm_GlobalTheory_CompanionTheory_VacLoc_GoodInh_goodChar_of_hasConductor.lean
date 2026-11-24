-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_GoodInh_goodChar_of_hasConductor
-- name    : GlobalTheory.CompanionTheory.VacLoc.GoodInh.goodChar_of_hasConductor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:27.917369+00:00
-- url     : https://prove2.me/theorems/1774cea1-f94b-4679-9d5b-5774842c84b5
-- title:
--   Good Inh: good Char of has Conductor
-- statement:
--   The Good Inh construction uses the good Char of has Conductor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DualNumberGraphFiltrationIsotropicOfSkew.lean#L11-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DualNumberGraphFiltrationIsotropicOfSkew.lean#L11-L93

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.GoodInh
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.VacLoc.GoodInh.goodChar_of_hasConductor (χ : AddChar k Circle) (c : kˣ) (hχ : HasConductor χ c) :
    GoodChar (Circle.coeHom.compAddChar χ) 𝒪[k] c := by sorry
