-- Prove2me | Theorems.Thm_GlobalTheory_SS_OrdMono_isUnit_of_dvd_pow
-- name    : GlobalTheory.SS.OrdMono.isUnit_of_dvd_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:27.598665+00:00
-- url     : https://prove2.me/theorems/e6b7d989-7327-43e5-8bc8-7be327fad31a
-- title:
--   Ord Mono: is Unit of dvd pow
-- statement:
--   The Ord Mono construction uses the is Unit of dvd pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/JacobianOrderMonotoneSemistableModel.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/JacobianOrderMonotoneSemistableModel.lean#L68-L77

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

theorem GlobalTheory.SS.OrdMono.isUnit_of_dvd_pow {B : Type} [CommRing B] {p s : B} (hp : Prime p) (h0 : p ∈ nonZeroDivisors B)
    (hs : ¬ p ∣ s) (k : ℕ) (h : s ∣ p ^ k) : IsUnit s := by sorry
