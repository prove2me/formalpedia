-- Prove2me | Theorems.Thm_GlobalTheory_WeilPullNoncomm_gm_manyChart
-- name    : GlobalTheory.WeilPullNoncomm.gm_manyChart
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:24:47.579389+00:00
-- url     : https://prove2.me/theorems/a469b08b-4bec-5e43-a99a-278099f33032
-- title:
--   Weil Pull Noncomm: gm many Chart
-- statement:
--   The Weil Pull Noncomm construction uses the gm many Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L29-L31

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

theorem GlobalTheory.WeilPullNoncomm.gm_manyChart {X Y : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) (f : Y ⟶ X) (y : Y) (i j : κ) :
    gm f y ((manyChart v).U i ⊓ (manyChart v).U j) ((manyChart v).g i j) = gm f y ⊤ (v i) * (gm f y ⊤ (v j))⁻¹ := by sorry
