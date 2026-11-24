-- Prove2me | Theorems.Thm_GlobalTheory_SectionRing_isDomain
-- name    : GlobalTheory.SectionRing.isDomain
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:55.818658+00:00
-- url     : https://prove2.me/theorems/da952f97-abac-4e00-a28f-82b647eba4ef
-- title:
--   Section Ring: is Domain
-- statement:
--   The Section Ring construction uses the is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L83-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsSectionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionRing
open Polynomial
variable {K A : Type} [Field K] [CommRing A] [Algebra K A]
variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]

theorem GlobalTheory.SectionRing.isDomain {B : Type} [CommRing B] [IsDomain B] (π : A →+* B)
    (hπ : ∀ n, ∀ a ∈ M n, π a = 0 → a = 0) : IsDomain (polyAlg M) := by sorry
