-- Prove2me | Theorems.Thm_MarkovChainCLT_isStrictlyStationary_chainMeasure
-- name    : MarkovChainCLT.isStrictlyStationary_chainMeasure
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:19:00.217157+00:00
-- url     : https://prove2.me/theorems/f0243795-7952-4530-8c4c-3dcf88b3358d
-- title:
--   The coordinate process of a chain started from an invariant measure is strictly stationary
-- statement:
--   Let $P$ be a Markov kernel with invariant probability measure $\pi$. Then the coordinate process $Y_i(\omega) = \omega_i$ on path space, under the law $\mathbb{P}_\pi$ of the chain started from $\pi$, is **strictly stationary**: for every $k$, the shifted sequence $(Y_k, Y_{k+1}, Y_{k+2}, \dots)$ has the same law, as a random element of $\mathsf{X}^{\mathbb{N}}$, as $(Y_0, Y_1, Y_2, \dots)$.
--
--   **Why this is the form actually needed.** Strict stationarity — equality of the laws of the *whole* shifted sequence, not just equality of finite-dimensional marginals one at a time — is the standing hypothesis of the classical central limit theorems for dependent sequences: Ibragimov and Linnik's theorem for strongly mixing sequences, Ibragimov's for $\rho$-mixing, Billingsley's for $\phi$-mixing, and Doukhan–Massart–Rio. Each of these is stated for a strictly stationary sequence, and the way they are applied to a Markov chain is: start the chain from $\pi$, observe that the coordinate process is then strictly stationary, and feed it in. This theorem is that observation.
--
--   It is also what makes the mixing coefficients of the chain well defined as functions of the lag alone: the definitions of $\alpha(n)$, $\rho(n)$ and $\phi(n)$ take a supremum over the split point $k$, and it is stationarity that makes the quantity being supremised independent of $k$.
--
--   **Proof.** By induction on $k$ from the one-step shift-invariance $\sigma_*\mathbb{P}_\pi = \mathbb{P}_\pi$. For $k = 0$ there is nothing to prove. For the step, the $(k{+}1)$-shift factors as the $k$-shift composed with $\sigma$, so pushing forward along it is pushing forward along $\sigma$ first — which leaves $\mathbb{P}_\pi$ unchanged — and then along the $k$-shift, which is the induction hypothesis.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 10 (invariant measures and stationarity); O. Kallenberg, Foundations of Modern Probability, 2nd ed., Springer 2002, Ch. 8; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem MarkovChainCLT.isStrictlyStationary_chainMeasure {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) :
    IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) := by sorry
