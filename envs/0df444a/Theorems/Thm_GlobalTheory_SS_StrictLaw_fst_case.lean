-- Prove2me | Theorems.Thm_GlobalTheory_SS_StrictLaw_fst_case
-- name    : GlobalTheory.SS.StrictLaw.fst_case
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:24.52562+00:00
-- url     : https://prove2.me/theorems/a7f95d42-6c40-4247-a1f1-d2e5c11c1528
-- title:
--   Strict Law: fst case
-- statement:
--   The Strict Law construction uses the fst case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStrictModelOfBirational.lean#L239-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStrictModelOfBirational.lean#L239-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [IsDomain R] [IsLocalRing R] [IsFractionRing R K]
  [IsAlgClosed (IsLocalRing.ResidueField R)]

theorem GlobalTheory.SS.StrictLaw.fst_case (M : Model R A) (hM : M.Irr) (f : A ⊗ A ⟶ A ⊗ A) (hf : f ≫ fst A A = fst A A)
    (h : GenIso (M.prod M) (M.prod M) f) :
    ∃ T : Set M.Y.left, IsOpen T ∧ (M.sp ∩ T).Nonempty ∧ ∀ V : Set M.Y.left, IsOpen V →
      ∀ x ∈ M.sp, x ∈ T → x ∈ V → ∃ z, (pr₁ M M).left z = x ∧ Good M f V z := by sorry
