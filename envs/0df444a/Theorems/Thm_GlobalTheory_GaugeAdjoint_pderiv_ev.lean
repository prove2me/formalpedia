-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_ev
-- name    : GlobalTheory.GaugeAdjoint.pderiv_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:13.963677+00:00
-- url     : https://prove2.me/theorems/c2cf12ee-5a51-4d02-9a22-8e1db8734c24
-- title:
--   Gauge Adjoint: pderiv ev
-- statement:
--   The Gauge Adjoint construction uses the pderiv ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L116-L121

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

theorem GlobalTheory.GaugeAdjoint.pderiv_ev {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) (s : Fin n × Fin d) :
    pderiv k s (ev a f) = ∑ j, ∑ i, ev a (pderiv k (j, i) f) * pderiv k s (a j i) := by sorry
