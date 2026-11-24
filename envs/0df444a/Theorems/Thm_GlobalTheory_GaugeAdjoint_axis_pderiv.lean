-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pderiv
-- name    : GlobalTheory.GaugeAdjoint.axis_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:17.551452+00:00
-- url     : https://prove2.me/theorems/0d98746e-e2c2-4831-9b56-d9a1e52872ff
-- title:
--   Gauge Adjoint: axis pderiv
-- statement:
--   The Gauge Adjoint construction uses the axis pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L261-L267

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

theorem GlobalTheory.GaugeAdjoint.axis_pderiv (φ : PS k 1 d) (i : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), i) φ)) =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) φ) := by sorry
