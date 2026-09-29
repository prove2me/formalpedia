-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellGraphCenterA_qJetBox_contains
-- name    : GeneralCK.Certificates.E8TAxisFirstCellGraphCenterA.qJetBox_contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T23:45:54.543507+00:00
-- url     : https://prove2.me/theorems/5c6b372b-0deb-44b1-8418-29f6a099009f
-- title:
--   E8 inverse derivative enclosure for the first-cell center A input
-- statement:
--   At dyadic precision $160$, let $I$ be the saved alpha interval of the first-cell center A input. For every real $a>0$ contained in $I$, the six literal intervals of its qJetBox enclose the value and first five components of the canonical E8 inverse jet at the stable slope $Y(a)$. Each enclosure is the exact source dyadic interval, with denominator $2^{160}$.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellGraphCenterA.lean#L388-L395

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_first_cell_jet_graphs
import Definitions.Def_GeneralCK_E8_semantic_core
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneContinuity

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisFirstCellGraphCenterA
open DyadicInterval E8TAxisStableInterval E8TAxisFirstCellPaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem GeneralCK.Certificates.E8TAxisFirstCellGraphCenterA.qJetBox_contains {a : ℝ} (ha : centerAInput.alpha.Contains a) (hapos : 0 < a) :
    qJetBox.Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by sorry
