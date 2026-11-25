-- Prove2me | Theorems.Thm_GlobalTheory_WeilPullNoncomm_heisEquiv_mul
-- name    : GlobalTheory.WeilPullNoncomm.heisEquiv_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:47.125803+00:00
-- url     : https://prove2.me/theorems/3d453bea-d7ee-4889-ba1e-5811d02ec154
-- title:
--   Weil Pull Noncomm: heis Equiv mul
-- statement:
--   The Weil Pull Noncomm construction uses the heis Equiv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L188-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L188-L190

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

theorem GlobalTheory.WeilPullNoncomm.heisEquiv_mul {S : Scheme.{0}} {T : Over S} (x y : T ⟶ heisObj S) :
    heisEquiv T (x * y) = heisEquiv T x * heisEquiv T y := by sorry
