-- Prove2me | Theorems.Thm_MarkovChainCLT_memLp_two_and_logMoment_sub_const
-- name    : MarkovChainCLT.memLp_two_and_logMoment_sub_const
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:27:27.752046+00:00
-- url     : https://prove2.me/theorems/2fda02d9-aaa7-4590-8ac3-40847fa612bb
-- title:
--   The $f^2\log^+|f|$ moment implies $f \in L^2$ and survives centring
-- statement:
--   Let $\pi$ be a probability distribution on $\mathsf{X}$ and let $f$ be measurable with the Doukhan-Massart-Rio moment
--
--   $$E_\pi\left[f^2 \log^+|f|\right] < \infty .$$
--
--   Then two things follow, for every constant $c$:
--
--   1. $f \in L^2(\pi)$, i.e. $E_\pi f^2 < \infty$;
--   2. the shifted function $f - c$ satisfies the same log-moment, $E_\pi\left[(f-c)^2 \log^+|f-c|\right] < \infty$.
--
--   For (1), split on $|f| \le e$ and $|f| > e$: on the first region $f^2 \le e^2$ and $\pi$ is finite, while on the second $\log^+|f| = \log|f| > 1$, so $f^2 \le f^2\log^+|f|$. Hence the pointwise bound $f^2 \le e^2 + f^2\log^+|f|$, whose right-hand side is integrable. Note that the log-moment alone genuinely carries this information: $\log^+$ vanishes on $\{|f| \le 1\}$, and it is finiteness of $\pi$ that controls the integral there.
--
--   For (2), use $|f - c| \le |f| + |c|$, the subadditivity $\log^+(u+v) \le \log 2 + \log^+ u + \log^+ v$, and $(u+v)^2 \le 2(u^2+v^2)$ to dominate $(f-c)^2\log^+|f-c|$ by a linear combination of the integrable functions $1$, $f^2$, $\log^+|f|$ and $f^2\log^+|f|$; here $\log^+|f| \le f^2\log^+|f|$ pointwise, because $\log^+$ vanishes where $f^2 < 1$.
--
--   This is the bookkeeping that lets Corollary 3 feed the *centred* functional $Y_n = f(X_n) - E_\pi f$ into Theorem 6, which is stated for centred sequences, while the corollary's hypothesis is a moment condition on $f$ itself. The $L^2$ conclusion is what makes the asymptotic variance $\sigma_f^2$ meaningful.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4, Theorem 6 and Corollary 3 (arXiv v2 p. 11): Theorem 6 (Doukhan, Massart & Rio 1994) assumes E[Y_0^2 log^+|Y_0|] < infinity for the centred stationary sequence, while Corollary 3 assumes E_pi[f^2 log^+|f|] < infinity.

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.memLp_two_and_logMoment_sub_const {X : Type*} [MeasurableSpace X]
    (π : Measure X) [IsProbabilityMeasure π] (f : X → ℝ) (hf : Measurable f)
    (hmom : Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) (c : ℝ) :
    MemLp f 2 π ∧ Integrable (fun x => (f x - c) ^ 2 * Real.posLog |f x - c|) π := by sorry
