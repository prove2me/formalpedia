-- Prove2me | Theorems.Thm_GlobalTheory_WeilPullNoncomm_manyChart_iso
-- name    : GlobalTheory.WeilPullNoncomm.manyChart_iso
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:07:41.373135+00:00
-- url     : https://prove2.me/theorems/7dc60c82-232f-4ba7-a0f6-e1c62d9dd6e2
-- title:
--   Weil Pull Noncomm: many Chart iso
-- statement:
--   The Weil Pull Noncomm construction uses the many Chart iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L41-L49

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

theorem GlobalTheory.WeilPullNoncomm.manyChart_iso {X Y : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) (F : X ⟶ Y) :
    LBIso (manyChart v) ((oneChart Y).pull F) := by sorry
