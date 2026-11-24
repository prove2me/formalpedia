-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_left
-- name    : GlobalTheory.GaugeAdjoint.pderiv_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:27.286205+00:00
-- url     : https://prove2.me/theorems/b9d840b3-7c0d-4945-92ef-d6c8570cff86
-- title:
--   Gauge Adjoint: pderiv left
-- statement:
--   The Gauge Adjoint construction uses the pderiv left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L246-L251

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

theorem GlobalTheory.GaugeAdjoint.pderiv_left {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d)
    (i : Fin d) :
    pderiv k ((1 : Fin 2), i) (ev (n := 2) ![comp1 φ (pt k d 0), pt k d 1] f) =
      ev (n := 2) ![comp1 φ (pt k d 0), pt k d 1] (pderiv k ((1 : Fin 2), i) f) := by sorry
