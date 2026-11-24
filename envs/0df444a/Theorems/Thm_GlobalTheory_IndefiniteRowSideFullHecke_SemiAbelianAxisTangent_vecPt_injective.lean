-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianAxisTangent_vecPt_injective
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecPt_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:16:03.341814+00:00
-- url     : https://prove2.me/theorems/c5411c32-cb04-4044-8544-8cdc514235c7
-- title:
--   Semi Abelian Axis Tangent: vec Pt injective
-- statement:
--   The Semi Abelian Axis Tangent construction uses the vec Pt injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L135-L139

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SemiAbelianAxisTangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (d : ℕ)

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecPt_injective {A : Type} [CommRing A] [Algebra S A] :
    Function.Injective (vecPt x0 d : (Fin d → A) → _) := by sorry
