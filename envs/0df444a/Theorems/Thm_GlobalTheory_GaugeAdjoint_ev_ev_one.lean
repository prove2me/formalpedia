-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_one
-- name    : GlobalTheory.GaugeAdjoint.ev_ev_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:03.796238+00:00
-- url     : https://prove2.me/theorems/8eb9a5f3-84be-4fc4-8d13-b363bffcafcc
-- title:
--   Gauge Adjoint: ev ev one
-- statement:
--   The Gauge Adjoint construction uses the ev ev one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L155-L162

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

theorem GlobalTheory.GaugeAdjoint.ev_ev_one {x : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k 1 d) :
    ev b (ev ![x] f) = ev ![fun i => ev b (x i)] f := by sorry
