-- Prove2me | Theorems.Thm_GlobalTheory_WeilPullNoncomm_weilIs_oneChart
-- name    : GlobalTheory.WeilPullNoncomm.weilIs_oneChart
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:50.571146+00:00
-- url     : https://prove2.me/theorems/0db71321-8a2f-5069-8c3a-3dec820b8093
-- title:
--   Weil Pull Noncomm: weil Is one Chart
-- statement:
--   The Weil Pull Noncomm construction uses the weil Is one Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L59-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L59-L89

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

theorem GlobalTheory.WeilPullNoncomm.weilIs_oneChart (hu : ∀ u : Γ(G.left, ⊤)ˣ, ∃ a : Γ(S, ⊤)ˣ, u = pullU G.hom ⊤ a) {T : Over S} [IsIso T.hom]
    (k : ℤ) (x y : T ⟶ G) : WeilIs G (oneChart _) k x y 1 := by sorry
