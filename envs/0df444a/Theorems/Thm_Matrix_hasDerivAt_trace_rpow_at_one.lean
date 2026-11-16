-- Prove2me | Theorems.Thm_Matrix_hasDerivAt_trace_rpow_at_one
-- name    : Matrix.hasDerivAt_trace_rpow_at_one
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-16T01:59:04.192791+00:00
-- url     : https://prove2.me/theorems/ba95fad0-06b3-4372-aeab-72a4c5e6ffba
-- title:
--   Trace-power derivative at exponent one for moving singular positive matrices
-- statement:
--   Let $H:\mathbb R\to M_n(\mathbb C)$ be a family of positive semidefinite matrices on a nonzero finite dimensional space. Suppose $H$ is continuous at $1$ and the scalar function $\alpha\mapsto\operatorname{Tr}H(\alpha)$ is differentiable there with derivative $d$. Then
--   $$\left.\frac{d}{d\alpha}\operatorname{Tr}\bigl(H(\alpha)^\alpha\bigr)\right|_{\alpha=1}
--   =d+\operatorname{Tr}\bigl(H(1)\log H(1)\bigr).$$
--   The trace functions are real valued. The power is defined by the continuous functional calculus, and $x\log x$ is extended continuously at $x=0$ by the value $0$. No invertibility or constant-rank hypothesis is required, and no derivative of the individual matrix entries of $H$ is assumed.
--
--   This trace-power differentiation principle isolates the singular-matrix analytic step in the relative entropy limit of quantum recovery inequalities. It is a supporting analytic lemma; it does not itself assert the quantum entropy difference formula.
-- source:
--   Supporting analytic lemma for the differentiation of the trace power in Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 12.4.1, Eq.(12.58), p.374, and Eq.(12.57), p.373; https://arxiv.org/abs/1106.1445v8 . The displayed general trace-power derivative is the auxiliary lemma formalized here, not a verbatim restatement of Lemma 12.4.1.

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Slope
open Matrix
open scoped MatrixOrder ComplexOrder Topology Matrix.Norms.L2Operator

namespace Matrix
theorem hasDerivAt_trace_rpow_at_one {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : ℝ → Matrix n n ℂ) (hH : ContinuousAt H 1)
    (hPSD : ∀ α, (H α).PosSemidef) (d : ℝ)
    (hD : HasDerivAt (fun α => (H α).trace.re) d 1) :
    HasDerivAt (fun α => (cfc (fun x : ℝ => x^α) (H α)).trace.re)
      (d+(cfc (fun x : ℝ => x*Real.log x) (H 1)).trace.re) 1 := by sorry
end Matrix
