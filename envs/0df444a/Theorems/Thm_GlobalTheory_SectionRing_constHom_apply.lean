-- Prove2me | Theorems.Thm_GlobalTheory_SectionRing_constHom_apply
-- name    : GlobalTheory.SectionRing.constHom_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:16.163988+00:00
-- url     : https://prove2.me/theorems/6ad8cb04-565b-52b6-b4da-609ad04e1619
-- title:
--   Section Ring: const Hom apply
-- statement:
--   The Section Ring construction uses the const Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L107-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L107-L107

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)

theorem GlobalTheory.SectionRing.constHom_apply (U : X.Opens) (a : K) : constHom p U a = constFn p U a := by sorry
