-- Prove2me | Theorems.Thm_GlobalTheory_Frames_Model_appLE_id_apply
-- name    : GlobalTheory.Frames.Model.appLE_id_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:39:25.216265+00:00
-- url     : https://prove2.me/theorems/6ae3726b-7a71-48bd-b55c-b1ac9aa04744
-- title:
--   Model: app LE id apply
-- statement:
--   The Model construction uses the app LE id apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L247-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L247-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.Frames.Model.appLE_id_apply (X : Scheme.{0}) (U : X.Opens) (h : U ≤ 𝟙 X ⁻¹ᵁ U) (z : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom z = z := by sorry
