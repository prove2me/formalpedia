-- Prove2me | Theorems.Thm_GlobalTheory_WeilPullNoncomm_gm_eq_one_of_commIsOf
-- name    : GlobalTheory.WeilPullNoncomm.gm_eq_one_of_commIsOf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:53.650665+00:00
-- url     : https://prove2.me/theorems/bdf7d8c6-bee6-513e-b269-1701f7ba8b37
-- title:
--   Weil Pull Noncomm: gm eq one of comm Is Of
-- statement:
--   The Weil Pull Noncomm construction uses the gm eq one of comm Is Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L104-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L104-L133

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

theorem GlobalTheory.WeilPullNoncomm.gm_eq_one_of_commIsOf (u : Γ(G.left, ⊤)ˣ) {T : Over S}
    {θx θy : ThetaGrp G (manyChart (fun b : Bool => if b then u else 1)) 1 T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf G _ 1 θx θy c) (hn : θx.pt * θy.pt ≠ θy.pt * θx.pt) (z : T.left) :
    ∃ r : T.left ⟶ G.left, gm r z ⊤ u = 1 := by sorry
