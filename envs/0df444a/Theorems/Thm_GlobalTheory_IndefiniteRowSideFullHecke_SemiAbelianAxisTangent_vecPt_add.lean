-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianAxisTangent_vecPt_add
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecPt_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:17:05.977402+00:00
-- url     : https://prove2.me/theorems/812d582a-a0a6-46d0-ba3b-4cf687ac15c6
-- title:
--   Semi Abelian Axis Tangent: vec Pt add
-- statement:
--   The Semi Abelian Axis Tangent construction uses the vec Pt add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L123-L128

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecPt_add {A : Type} [CommRing A] [Algebra S A] (v w : Fin d → A) :
    vecPt x0 d (v + w) = vecPt x0 d v * vecPt x0 d w := by sorry
