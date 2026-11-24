-- Prove2me | Theorems.Thm_GlobalTheory_LocalizationIntegrallyClosedDomain_isIntegrallyClosed
-- name    : GlobalTheory.LocalizationIntegrallyClosedDomain.isIntegrallyClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:16:55.585526+00:00
-- url     : https://prove2.me/theorems/969cb534-6b36-43db-89e7-c371dd9b38be
-- title:
--   Localization Integrally Closed Domain: is Integrally Closed
-- statement:
--   The Localization Integrally Closed Domain construction uses the is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L72-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L72-L187

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
variable {B : Type} [CommRing B] {Q : Ideal B} [Q.IsPrime]
set_option maxHeartbeats 1600000

theorem GlobalTheory.LocalizationIntegrallyClosedDomain.isIntegrallyClosed
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q))
    [IsDomain (Localization.AtPrime Q)] :
    IsIntegrallyClosed (Localization.AtPrime Q) := by sorry
