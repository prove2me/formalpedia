-- Prove2me | Theorems.Thm_LogOfAnalyticFunction
-- name    : LogOfAnalyticFunction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:25:54.867302+00:00
-- url     : https://prove2.me/theorems/eaf55684-4e89-4107-beb9-2f7cdf373cbf
-- title:
--   Existence of an analytic logarithm $J_B$ with $\operatorname{Re} J_B = \log\|B\| - \log\|B(0)\|$
-- statement:
--   Let $0 < r < R$ be real numbers and let $B : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of the closed disk $\overline{D}(0,R)$ and nonvanishing on all of $\overline{D}(0,R)$.
--
--   Then there exists a function $J_B : \mathbb{C} \to \mathbb{C}$, analytic on the open disk $D(0,R)$, such that:
--
--   - $J_B(0) = 0$;
--   - $J_B'(z) = B'(z)/B(z)$ for all $z$ in the closed disk $\overline{D}(0,r)$;
--   - for all $z$ in the open disk $D(0,R)$,
--   $$\log \|B(z)\| - \log \|B(0)\| = \operatorname{Re}\, J_B(z).$$
--
--   Thus $J_B$ is a normalized analytic branch of $\log(B(z)/B(0))$: its derivative is the logarithmic derivative of $B$ and its real part recovers $\log|B|$ up to the constant $\log|B(0)|$. In the module `Zeta23.FromPNTPlus.StrongPNTPrefix` this is the key input to `Zeta23.WeilEF.norm_logDeriv_Cf_le`, where a Borel–Carathéodory-type argument applied to $J_B$ (with $B$ the zero-free factor $C_f$) converts an upper bound on $\log|B|$ into a bound on $B'/B$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/StrongPNTPrefix.lean#L124-L181

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

theorem LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by sorry
