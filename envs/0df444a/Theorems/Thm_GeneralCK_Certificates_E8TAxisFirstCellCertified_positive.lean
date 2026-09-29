-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellCertified_positive
-- name    : GeneralCK.Certificates.E8TAxisFirstCellCertified.positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:55:35.363609+00:00
-- url     : https://prove2.me/theorems/3a4829ae-8600-4bf1-8648-720b27ea7476
-- title:
--   Unconditional E8 positivity throughout the certified first cell
-- statement:
--   For real $s,t$ satisfying $s_{\rm lower}\le s\le3/40$ and $t_{\rm lower}\le t\le1/50$, the regularized E8 determinant derivative e8RegularDeltaT$(s,t)$ is strictly positive. The two lower endpoints are the exact rational constants sLower and tLower in the published first-cell geometry (approximately $0.0675$ and $0.01$).
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellCertified.lean#L74-L76

import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisFirstCellCertified
open GeneralCK Set E8TAxisOneCellGeometry E8TAxisFirstCellCertifiedArithmetic
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor

theorem GeneralCK.Certificates.E8TAxisFirstCellCertified.positive {s t : ℝ} (h : InFirstCell s t) :
    0 < e8RegularDeltaT s t := by sorry
