-- Prove2me | Theorems.Thm_GlobalTheory_TorusTranslate_appLE_app
-- name    : GlobalTheory.TorusTranslate.appLE_app
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:06:25.979281+00:00
-- url     : https://prove2.me/theorems/ce195d49-6011-4972-b303-aec5f97ff434
-- title:
--   Torus Translate: app LE app
-- statement:
--   The Torus Translate construction uses the app LE app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPointTranslatePure.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPointTranslatePure.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorusTranslate

theorem GlobalTheory.TorusTranslate.appLE_app {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (hm : ⊤ ≤ m ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)) :
    (m.appLE (f ⁻¹ᵁ U) ⊤ hm).hom ((f.app U).hom u) = (g.appLE U ⊤ hg).hom u := by sorry
