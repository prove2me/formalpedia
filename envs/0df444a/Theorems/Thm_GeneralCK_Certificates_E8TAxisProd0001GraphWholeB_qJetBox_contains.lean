-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001GraphWholeB_qJetBox_contains
-- name    : GeneralCK.Certificates.E8TAxisProd0001GraphWholeB.qJetBox_contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T02:56:51.06151+00:00
-- url     : https://prove2.me/theorems/b5fcf4e7-e384-415f-a2c7-8229dc05c9fd
-- title:
--   E8 inverse derivative enclosure for production cell 0001, whole B
-- statement:
--   At dyadic precision $160$, let $I$ be the stored alpha interval for the whole B input of E8 production cell 0001. For every real $a>0$ contained in $I$, the six intervals of qJetBox enclose the value and first five components of the canonical E8 inverse jet at the stable slope $Y(a)$. The dyadic interval denominator is $2^{160}$.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_E8_Prod0001_graph_mixed_data
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
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

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisProd0001GraphWholeB
open DyadicInterval E8TAxisStableInterval E8TAxisProd0001PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem GeneralCK.Certificates.E8TAxisProd0001GraphWholeB.qJetBox_contains {a : ℝ} (ha : wholeBInput.alpha.Contains a) (hapos : 0 < a) :
    qJetBox.Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by sorry
