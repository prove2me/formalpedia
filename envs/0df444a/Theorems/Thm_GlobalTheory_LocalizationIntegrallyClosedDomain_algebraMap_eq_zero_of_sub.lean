-- Prove2me | Theorems.Thm_GlobalTheory_LocalizationIntegrallyClosedDomain_algebraMap_eq_zero_of_sub
-- name    : GlobalTheory.LocalizationIntegrallyClosedDomain.algebraMap_eq_zero_of_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:11.801648+00:00
-- url     : https://prove2.me/theorems/4008a44f-0d11-404c-bf81-4b08acd3e031
-- title:
--   Localization Integrally Closed Domain: algebra Map eq zero of sub
-- statement:
--   The Localization Integrally Closed Domain construction uses the algebra Map eq zero of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L11-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.LocalizationIntegrallyClosedDomain
variable {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]

theorem GlobalTheory.LocalizationIntegrallyClosedDomain.algebraMap_eq_zero_of_sub (C : Subring B) (c : C)
    (h : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) c = 0) :
    algebraMap B (Localization.AtPrime Q) (c : B) = 0 := by sorry
