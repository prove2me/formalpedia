-- Prove2me | Theorems.Thm_GlobalTheory_FunDescent_exists_appTop_eq
-- name    : GlobalTheory.FunDescent.exists_appTop_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:32.475704+00:00
-- url     : https://prove2.me/theorems/c684b072-d8a7-466e-9cb9-709ecb3bb2e8
-- title:
--   Fun Descent: exists app Top eq
-- statement:
--   The Fun Descent construction uses the exists app Top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L44-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FunDescent

theorem GlobalTheory.FunDescent.exists_appTop_eq {X Y : Scheme.{0}} (π : X ⟶ Y) [EffectiveEpi π] (f : Γ(X, ⊤))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π →
      g₁.appTop.hom f = g₂.appTop.hom f) :
    ∃ a, π.appTop.hom a = f := by sorry
