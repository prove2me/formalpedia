-- Prove2me | Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_sum_of_isUnit
-- name    : GlobalTheory.SmoothLocusAdd.exists_sum_of_isUnit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:45:11.366192+00:00
-- url     : https://prove2.me/theorems/4562919b-2b75-53c3-bee9-405bf6d13171
-- title:
--   Smooth Locus Add: exists sum of is Unit
-- statement:
--   The Smooth Locus Add construction uses the exists sum of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L108-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L108-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open WeierstrassCurve.Projective

theorem GlobalTheory.SmoothLocusAdd.exists_sum_of_isUnit {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q S : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q))
    (hS : ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 →
      φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q))
    (i : Fin 3) (hi : IsUnit (S i)) :
    ∃ h : IsUnimodularSol (W.map ρ) S, ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Spec (.of C)),
      IsSumAt W (x ≫ ptHom W ρ P hP) (x ≫ ptHom W ρ Q hQ) (x ≫ ptHom W ρ S h) := by sorry
