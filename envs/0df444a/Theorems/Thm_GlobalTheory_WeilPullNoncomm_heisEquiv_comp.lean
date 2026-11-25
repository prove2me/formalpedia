-- Prove2me | Theorems.Thm_GlobalTheory_WeilPullNoncomm_heisEquiv_comp
-- name    : GlobalTheory.WeilPullNoncomm.heisEquiv_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:20.111784+00:00
-- url     : https://prove2.me/theorems/874a8090-904b-528c-b7c8-265f71b0b51d
-- title:
--   Weil Pull Noncomm: heis Equiv comp
-- statement:
--   The Weil Pull Noncomm construction uses the heis Equiv comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L192-L193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem GlobalTheory.WeilPullNoncomm.heisEquiv_comp {S : Scheme.{0}} {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ heisObj S) :
    heisEquiv T' (g ≫ x) = Heis.map g.left.appTop.hom (heisEquiv T x) := by sorry
