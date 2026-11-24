-- Prove2me | Theorems.Thm_GlobalTheory_SS_OrdMono_chain_model
-- name    : GlobalTheory.SS.OrdMono.chain_model
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:28.915251+00:00
-- url     : https://prove2.me/theorems/51515bd1-5f2c-4fe8-865b-aa9ba8a20f5e
-- title:
--   Ord Mono: chain model
-- statement:
--   The Ord Mono construction uses the chain model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/JacobianOrderMonotoneSemistableModel.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/JacobianOrderMonotoneSemistableModel.lean#L36-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfExtendsIdOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobianOrderMonotoneSemistableModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdMono
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
  {I : Type} [Fintype I] [DecidableEq I]

theorem GlobalTheory.SS.OrdMono.chain_model (M : Model R A) (D : I → VF A) (U : M.Y.left.Opens) (t t' : I → Γ(M.Y.left, U))
    (h : IsCoord M U t) : ∃ a, jm M D U t' = (M.j.app U).hom a * jm M D U t ∧ (IsUnit a → IsCoord M U t') := by sorry
