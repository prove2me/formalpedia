-- Prove2me | Theorems.Thm_GlobalTheory_TorusTranslate_appLE_res
-- name    : GlobalTheory.TorusTranslate.appLE_res
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:53.839814+00:00
-- url     : https://prove2.me/theorems/400a6b08-8b43-4a42-9f30-c129a547e87a
-- title:
--   Torus Translate: app LE res
-- statement:
--   The Torus Translate construction uses the app LE res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPointTranslatePure.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPointTranslatePure.lean#L29-L32

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

theorem GlobalTheory.TorusTranslate.appLE_res {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U W : Y.Opens) (h : W ≤ U)
    (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ m ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h u).val = (m.appLE U ⊤ hg).hom u.val := by sorry
