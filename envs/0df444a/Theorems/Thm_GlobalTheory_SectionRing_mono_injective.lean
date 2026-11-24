-- Prove2me | Theorems.Thm_GlobalTheory_SectionRing_mono_injective
-- name    : GlobalTheory.SectionRing.mono_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:52.723363+00:00
-- url     : https://prove2.me/theorems/e8bceed2-f803-4d29-b197-367ac9b5eff1
-- title:
--   Section Ring: mono injective
-- statement:
--   The Section Ring construction uses the mono injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L31-L32

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

theorem GlobalTheory.SectionRing.mono_injective (e : ℕ) : Function.Injective (mono M e) := by sorry
