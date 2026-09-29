-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8InverseJet5Bridge_e8QCanonicalJet5_soundAt_unconditional
-- name    : GeneralCK.Certificates.E8InverseJet5Bridge.e8QCanonicalJet5_soundAt_unconditional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T23:18:57.674516+00:00
-- url     : https://prove2.me/theorems/f50445cd-269c-45c3-b52f-38ac0c1f9641
-- title:
--   Unconditional fifth-order soundness of the E8 inverse jet
-- statement:
--   Let $\Theta$ be the E8 slope function, let $Q$ be its positive inverse on $\Theta((0,\infty))$, and let $J$ be the explicit canonical inverse jet built from the first five derivatives of $\Theta$. For every $y\in\Theta((0,\infty))$, all five derivative links hold at $y$: the derivative of $J_k$ is $J_{k+1}(y)$ for $k=0,1,2,3,4$. Thus the six components of $J$, starting with $Q$, are its actual raw derivatives through order five, without an additional higher-smoothness assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8InverseJet5Bridge.lean#L167-L171

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_derivative_semantics
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8InverseJet5Bridge
open GeneralCK Set

theorem GeneralCK.Certificates.E8InverseJet5Bridge.e8QCanonicalJet5_soundAt_unconditional
    {y : ℝ} (hy : y ∈ e8SlopeRange) :
    (e8QJet5 e8ThetaCanonicalJet5).SoundAt y := by sorry
