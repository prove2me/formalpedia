-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianAxisTangent_vecEquiv_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecEquiv_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:59.997409+00:00
-- url     : https://prove2.me/theorems/2fdb415a-b6e4-41a4-a75d-1bca5c11d478
-- title:
--   Semi Abelian Axis Tangent: vec Equiv one
-- statement:
--   The Semi Abelian Axis Tangent construction uses the vec Equiv one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L94-L96

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecEquiv_one {X : Scheme.{0}} {d : ℕ} {T : Over X} :
    vecEquiv T (1 : T ⟶ vecObj X d) = 1 := by sorry
