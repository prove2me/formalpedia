-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_comp1
-- name    : GlobalTheory.GaugeAdjoint.pderiv_comp1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:18.882414+00:00
-- url     : https://prove2.me/theorems/bbfbb5ca-f9d6-433e-9fd9-2fb55faa56fa
-- title:
--   Gauge Adjoint: pderiv comp1
-- statement:
--   The Gauge Adjoint construction uses the pderiv comp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L236-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L236-L244

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

theorem GlobalTheory.GaugeAdjoint.pderiv_comp1 (φ : Pt k 1 d) (j j' : Fin n) (i l : Fin d) :
    pderiv k (j, i) (comp1 φ (pt k d j') l) =
      if j' = j then ev ![pt k d j'] (pderiv k ((0 : Fin 1), i) (φ l)) else 0 := by sorry
