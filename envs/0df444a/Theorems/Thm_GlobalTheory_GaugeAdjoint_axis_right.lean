-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_right
-- name    : GlobalTheory.GaugeAdjoint.axis_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:19.224045+00:00
-- url     : https://prove2.me/theorems/1d521a67-c824-4cf6-b206-4688b52b9645
-- title:
--   Gauge Adjoint: axis right
-- statement:
--   The Gauge Adjoint construction uses the axis right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L214-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L214-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
variable {k : Type} [CommRing k] {d m n p : ℕ}

theorem GlobalTheory.GaugeAdjoint.axis_right {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0, comp1 φ (pt k d 1)] f) =
      ev (n := 1) ![pt k d 0, 0] f := by sorry
