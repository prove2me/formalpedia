-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_left
-- name    : GlobalTheory.GaugeAdjoint.axis_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:13.887839+00:00
-- url     : https://prove2.me/theorems/56086c74-ee12-4ce3-9f44-7a9ae3058e3a
-- title:
--   Gauge Adjoint: axis left
-- statement:
--   The Gauge Adjoint construction uses the axis left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L192-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L192-L212

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

theorem GlobalTheory.GaugeAdjoint.axis_left {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![comp1 φ (pt k d 0), pt k d 1] f) =
      ev (n := 1) ![comp1 φ (pt k d 0)] (ev (n := 1) ![pt k d 0, 0] f) := by sorry
