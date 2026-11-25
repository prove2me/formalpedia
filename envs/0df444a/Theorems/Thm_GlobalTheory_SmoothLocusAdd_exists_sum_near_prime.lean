-- Prove2me | Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_sum_near_prime
-- name    : GlobalTheory.SmoothLocusAdd.exists_sum_near_prime
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:47:13.677798+00:00
-- url     : https://prove2.me/theorems/e6edab3e-5429-41c3-8057-992e500686b1
-- title:
--   Smooth Locus Add: exists sum near prime
-- statement:
--   The Smooth Locus Add construction uses the exists sum near prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L132-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L132-L178

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

theorem GlobalTheory.SmoothLocusAdd.exists_sum_near_prime {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q)) (z : Spec (.of C)) :
    ∃ (V : Scheme.{0}) (j : V ⟶ Spec (.of C)) (_ : IsOpenImmersion j) (f : V ⟶ scheme W),
      z ∈ Set.range j ∧ f ≫ toSpec W = j ≫ Spec.map (CommRingCat.ofHom ρ) ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V),
          IsSumAt W (x ≫ j ≫ ptHom W ρ P hP) (x ≫ j ≫ ptHom W ρ Q hQ) (x ≫ f) := by sorry
