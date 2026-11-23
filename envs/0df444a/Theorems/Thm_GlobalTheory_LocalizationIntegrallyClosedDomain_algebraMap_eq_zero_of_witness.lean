-- Prove2me | Theorems.Thm_GlobalTheory_LocalizationIntegrallyClosedDomain_algebraMap_eq_zero_of_witness
-- name    : GlobalTheory.LocalizationIntegrallyClosedDomain.algebraMap_eq_zero_of_witness
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:57.86267+00:00
-- url     : https://prove2.me/theorems/5359b26d-43cd-4ba0-a5e7-29310a897dd1
-- title:
--   Localization Integrally Closed Domain: algebra Map eq zero of witness
-- statement:
--   The Localization Integrally Closed Domain construction uses the algebra Map eq zero of witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L20-L24

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

theorem GlobalTheory.LocalizationIntegrallyClosedDomain.algebraMap_eq_zero_of_witness (C : Subring B) (u e : C) (hu : (u : B) ∉ Q)
    (h : u * e = 0) :
    algebraMap C (Localization.AtPrime (Q.comap C.subtype)) e = 0 := by sorry
