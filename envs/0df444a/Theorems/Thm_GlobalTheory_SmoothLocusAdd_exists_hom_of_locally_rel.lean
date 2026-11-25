-- Prove2me | Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_hom_of_locally_rel
-- name    : GlobalTheory.SmoothLocusAdd.exists_hom_of_locally_rel
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:46:21.242052+00:00
-- url     : https://prove2.me/theorems/d276aba0-56b1-435c-ae13-460d96536b03
-- title:
--   Smooth Locus Add: exists hom of locally rel
-- statement:
--   The Smooth Locus Add construction uses the exists hom of locally rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L19-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L19-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve

theorem GlobalTheory.SmoothLocusAdd.exists_hom_of_locally_rel {T Y S : Scheme.{0}} [IsReduced T] (t : T ⟶ S) (s : Y ⟶ S)
    [IsSeparated s]
    (Rel : ∀ (k : Type) [Field k], (Spec (.of k) ⟶ T) → (Spec (.of k) ⟶ Y) → Prop)
    (huniq : ∀ (k : Type) [Field k] x y y', Rel k x y → Rel k x y' → y = y')
    (H : ∀ z : T, ∃ (V : Scheme.{0}) (j : V ⟶ T) (_ : IsOpenImmersion j) (f : V ⟶ Y),
      z ∈ Set.range j ∧ f ≫ s = j ≫ t ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V), Rel k (x ≫ j) (x ≫ f)) :
    ∃ f : T ⟶ Y, f ≫ s = t ∧ ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), Rel k x (x ≫ f) := by sorry
