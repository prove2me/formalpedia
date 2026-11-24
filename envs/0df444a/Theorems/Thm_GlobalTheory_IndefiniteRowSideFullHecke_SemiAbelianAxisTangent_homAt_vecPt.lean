-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianAxisTangent_homAt_vecPt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.homAt_vecPt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:59.401724+00:00
-- url     : https://prove2.me/theorems/b5ff8f43-5389-41a2-92ee-7baab9ff919b
-- title:
--   Semi Abelian Axis Tangent: hom At vec Pt
-- statement:
--   The Semi Abelian Axis Tangent construction uses the hom At vec Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L112-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SemiAbelianAxisTangent.lean#L112-L121

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.homAt_vecPt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B]
    (f : A →ₐ[S] B) (v : Fin d → A) : homAt x0 f ≫ vecPt x0 d v = vecPt x0 d fun j => f (v j) := by sorry
