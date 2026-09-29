-- Prove2me | Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_stationary_clt_of_uniformlyErgodic
-- name    : MarkovChainCLT.satisfiesCLT_of_stationary_clt_of_uniformlyErgodic
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T22:36:28.330364+00:00
-- url     : https://prove2.me/theorems/e4db98b6-e462-4cd2-8b5e-2c1790690f77
-- title:
--   A uniformly ergodic chain forgets its initial distribution in the CLT
-- statement:
--   **Removing the stationarity assumption from a Markov chain CLT.** Suppose a uniformly ergodic chain with invariant law $\pi$ satisfies the central limit theorem when *started from $\pi$*:
--   $$\sqrt n\,\bigl(\bar f_n - \mathbb E_\pi f\bigr) \;\xrightarrow{\ d\ }\; N(0,v) \qquad \text{under } \mathbb P_\pi .$$
--   Then the same limit holds under **every** initial distribution $\lambda$ — that is, `SatisfiesCLT P π f` holds, with the same asymptotic variance $v$.
--
--   **Why this step is needed.** Every proof of a Markov chain CLT — via martingale approximation, via mixing coefficients, via regeneration — produces the limit for the stationary chain, because that is the only chain for which the summands form a stationary sequence. The statement one wants, however, quantifies over all starting distributions. This lemma is the bridge, and it is where uniform ergodicity earns its keep.
--
--   **Proof.** Write $c = f - \mathbb E_\pi f$, $S_k(\omega) = \sum_{i=1}^{k} c(\omega_i)$, so that the statistic is $T_k = k^{-1/2} S_k$, and let $\sigma^m$ be the shift $(\sigma^m\omega)_j = \omega_{j+m}$. Splitting the sum at time $m$ gives the exact identity
--   $$T_{m+n} \;=\; \frac{S_m}{\sqrt{m+n}} \;+\; \sqrt{\tfrac{n}{m+n}}\;\bigl(T_n\circ\sigma^m\bigr).$$
--   Fix a bounded Lipschitz test function $F$ — by the portmanteau theorem these suffice to test weak convergence — and set $c_n = \sqrt{n/(m+n)}$. Then
--   $$\bigl|\mathbb E_\lambda F(T_{m+n}) - \textstyle\int F\,dN(0,v)\bigr| \;\le\; \underbrace{\bigl|\mathbb E_\lambda\bigl[F(T_{m+n}) - F(c_n\,T_n\!\circ\!\sigma^m)\bigr]\bigr|}_{(\mathrm I)} + \underbrace{\bigl|\mathbb E_\lambda F(c_n T_n\!\circ\!\sigma^m) - \mathbb E_\pi F(c_n T_n)\bigr|}_{(\mathrm{II})} + \underbrace{\bigl|\mathbb E_\pi F(c_nT_n) - \textstyle\int F\,dN\bigr|}_{(\mathrm{III})}.$$
--
--   *(I) vanishes* because the two arguments of $F$ differ by $S_m/\sqrt{m+n}$, a **fixed** random variable divided by $\sqrt{m+n}$, hence tending to $0$ in probability with no integrability assumption; $F$ is Lipschitz and bounded, so the bounded convergence theorem for convergence in probability applies.
--
--   *(II) is where uniform ergodicity enters*, and it is bounded **uniformly in $n$**: pushing $\mathbb P_\lambda$ forward by $\sigma^m$ and using the data-processing inequality, the path law of the $\lambda$-chain observed from time $m$ is within total variation $R t^m$ of the stationary path law, so testing against any function bounded by $\|F\|_\infty$ costs at most $2\|F\|_\infty R t^m$. Note that this term is *not* asymptotically negligible for fixed $m$ — it is made small by choosing $m$ large first, which is possible precisely because the rate $Rt^m$ does not depend on the starting point.
--
--   *(III) vanishes* by Slutsky's theorem: $c_n \to 1$ deterministically and $T_n \to N(0,v)$ in distribution under $\mathbb P_\pi$.
--
--   Given $\varepsilon>0$, choose $m \ge 1$ with $2\|F\|_\infty R t^m < \varepsilon/3$, then $n$ large enough that (I) and (III) are each below $\varepsilon/3$. Since every large $k$ is of the form $m+n$, this is exactly the required convergence.
--
--   **A remark on what is not needed.** Neither tightness of the family $\{T_n\}$ nor any moment bound on $f$ beyond what `hclt` already provides is used: the scaling factor $c_n$ is transferred to the stationary side *before* the total-variation comparison, so Slutsky's theorem does all the work on the side where convergence is known.
-- source:
--   L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728, Section 3; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 2 and Corollary 5.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.satisfiesCLT_of_stationary_clt_of_uniformlyErgodic {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (huni : UniformlyErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v)) :
    SatisfiesCLT P π f := by sorry
