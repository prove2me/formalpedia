-- Prove2me | Theorems.Thm_GlobalTheory_LieEtale_isLieEigen_iff
-- name    : GlobalTheory.LieEtale.isLieEigen_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:04:52.418267+00:00
-- url     : https://prove2.me/theorems/ae4152ea-8599-4a8f-8059-aad200928e55
-- title:
--   Lie Etale: is Lie Eigen iff
-- statement:
--   The Lie Etale construction uses the is Lie Eigen iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L144-L147

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)

theorem GlobalTheory.LieEtale.isLieEigen_iff (v : epsPt x ⟶ G) :
    IsLieEigen act x τ v ↔ Eig (epsPtZero x) (epsPtScale x) act.act τ v := by sorry
