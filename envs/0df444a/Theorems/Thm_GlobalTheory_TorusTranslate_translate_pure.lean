-- Prove2me | Theorems.Thm_GlobalTheory_TorusTranslate_translate_pure
-- name    : GlobalTheory.TorusTranslate.translate_pure
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:27:30.632629+00:00
-- url     : https://prove2.me/theorems/ca50a55b-cc39-4c77-84ca-8f8715303fd5
-- title:
--   Torus Translate: translate pure
-- statement:
--   The Torus Translate construction uses the translate pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPointTranslatePure.lean#L76-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPointTranslatePure.lean#L76-L126

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
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G) {Z : Over S}

theorem GlobalTheory.TorusTranslate.translate_pure (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (V : E.B.left.Opens) (hV : IsAffineOpen V) (hle : V ≤ E.chart j) (α : E.X)
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (hs : ∀ β, β ≠ α → D.weight j V hV hle β s = 0)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom s =
      τ.left.appTop.hom (charUnit S E.X α).val * (x.left.appLE _ ⊤ h).hom s := by sorry
