-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisStableInterval_checked_stable_contains_canonical
-- name    : GeneralCK.Certificates.E8TAxisStableInterval.checked_stable_contains_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T23:37:06.595977+00:00
-- url     : https://prove2.me/theorems/f6e9c3a9-b9e1-4ad7-a9cd-8f300f0efbea
-- title:
--   Checked stable E8 intervals enclose all five inverse derivatives
-- statement:
--   Fix a dyadic precision $p$ and an Inputs record $i$ containing intervals for a parameter, its exponential, its logarithm, and $\log2$. Suppose the executable exponential and both logarithm checks accept, all five denominator lower bounds are positive, and the first-derivative lower bound of yBox is positive. For every positive $a$ in the parameter interval, the exact interval reparametrization eval(xBox,yBox) encloses all six components of the canonical E8 inverse jet at the stable slope $Y(a)$. This supplies the value and first five raw derivative enclosures used by each numerical cell graph.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisStableInterval.lean#L198-L216

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_interval_checkers
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

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisStableInterval
open DyadicInterval  E8TAxisReparamInterval

theorem GeneralCK.Certificates.E8TAxisStableInterval.checked_stable_contains_canonical {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl wL : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hL : logBoxCheck (ofInt p 2) i.logTwo wL = true)
    (hp : DenominatorsPositive i) (hyp : 0 < (yBox i).d1.lo)
    {a : ℝ} (ha : i.alpha.Contains a) (hapos : 0 < a) :
    (eval (xBox i) (yBox i)).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by sorry
