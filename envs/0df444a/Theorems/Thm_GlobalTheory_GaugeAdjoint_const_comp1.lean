-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_const_comp1
-- name    : GlobalTheory.GaugeAdjoint.const_comp1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:48.813286+00:00
-- url     : https://prove2.me/theorems/8b373bad-7ad5-401c-aa02-6dfedcfce04e
-- title:
--   Gauge Adjoint: const comp1
-- statement:
--   The Gauge Adjoint construction uses the const comp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L141-L145

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

theorem GlobalTheory.GaugeAdjoint.const_comp1 {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) {x : Pt k n d}
    (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) : constantCoeff (comp1 φ x i) = 0 := by sorry
