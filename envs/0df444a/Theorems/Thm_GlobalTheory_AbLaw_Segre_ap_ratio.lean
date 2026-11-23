-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_ratio
-- name    : GlobalTheory.AbLaw.Segre.ap_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:27.598514+00:00
-- url     : https://prove2.me/theorems/4b93cd3d-118e-42d8-beaf-9506ed53b685
-- title:
--   Segre: ap ratio
-- statement:
--   The Segre construction uses the ap ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L71-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem GlobalTheory.AbLaw.Segre.ap_ratio {U V : X.Opens} {x y : Γ(X, V)} {r : Γ(X, U)}
    (e : rs X (inf_le_right : U ⊓ V ≤ V) x =
      rs X (inf_le_left : U ⊓ V ≤ U) r * rs X (inf_le_right : U ⊓ V ≤ V) y)
    {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ p ⁻¹ᵁ V) :
    ap p h₂ x = ap p h₁ r * ap p h₂ y := by sorry
