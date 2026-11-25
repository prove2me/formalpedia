-- Prove2me | Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_sum
-- name    : GlobalTheory.SmoothLocusAdd.exists_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:44:57.401134+00:00
-- url     : https://prove2.me/theorems/1e14e863-f7ac-5dd3-9856-5d12cea23edd
-- title:
--   Smooth Locus Add: exists sum
-- statement:
--   The Smooth Locus Add construction uses the exists sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L180-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L180-L211

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
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem GlobalTheory.SmoothLocusAdd.exists_sum {T : Scheme.{0}} [IsReduced T] (p q : T ⟶ scheme W)
    (hpq : p ≫ toSpec W = q ≫ toSpec W)
    (np : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ p))
    (nq : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ q)) :
    ∃ s : T ⟶ scheme W, s ≫ toSpec W = p ≫ toSpec W ∧
      ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsSumAt W (x ≫ p) (x ≫ q) (x ≫ s) := by sorry
