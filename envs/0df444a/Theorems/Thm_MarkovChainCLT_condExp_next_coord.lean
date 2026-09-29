-- Prove2me | Theorems.Thm_MarkovChainCLT_condExp_next_coord
-- name    : MarkovChainCLT.condExp_next_coord
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:15:25.30419+00:00
-- url     : https://prove2.me/theorems/f4a8122d-e936-4b5b-addc-f18a00f80f6b
-- title:
--   The chain's conditional expectation given the past is one step of the kernel
-- statement:
--   **The Markov property as an identity of conditional expectations.** For a bounded measurable $h$ and every $k$,
--   $$\mathbb E\bigl[h(X_{k+1}) \,\big|\, \sigma(X_0,\dots,X_k)\bigr] \;=\; (Ph)(X_k) \qquad\text{almost surely},$$
--   where $(Ph)(x) = \int h\,dP(x,\cdot)$ and the conditioning $\sigma$-algebra is the pullback of the Borel structure on the first $k+1$ coordinates. This holds for every initial distribution.
--
--   **What it is for.** This is the hypothesis that turns Poisson-equation bookkeeping into a genuine martingale. If $g$ solves $g - Pg = \varphi - \mathbb E_\pi\varphi$ then
--   $$D_k \;=\; g(X_{k+1}) - (Pg)(X_k)$$
--   satisfies $\mathbb E[D_k \mid \sigma(X_0,\dots,X_k)] = 0$, i.e. $(D_k)$ is a martingale difference sequence for the natural filtration of the chain — exactly the input required by every martingale central limit theorem. It also gives orthogonality, $\mathbb E[D_jD_k] = 0$ for $j\ne k$, hence $\operatorname{Var}\bigl(\sum_{k<n}D_k\bigr) = \sum_{k<n}\mathbb E D_k^2$, the linear-in-$n$ variance bound behind the law of large numbers for the quadratic variation.
--
--   **Proof.** The candidate $(Ph)(X_k)$ is measurable with respect to $\sigma(X_0,\dots,X_k)$ — the coordinate map $\omega\mapsto\omega_k$ factors through the restriction to the first $k+1$ coordinates, and $x\mapsto\int h\,dP(x,\cdot)$ is measurable because integration against a kernel preserves measurability. It is integrable, being bounded by $\|h\|_\infty$. Finally, for every event $A$ in the conditioning $\sigma$-algebra the two set integrals agree,
--   $$\int_A h(X_{k+1})\,d\mathbb P \;=\; \int_A (Ph)(X_k)\,d\mathbb P,$$
--   which is the Markov property in integral form. The standard characterization of conditional expectation — a measurable, integrable function with the correct set integrals *is* the conditional expectation — then gives the claim.
-- source:
--   J. Neveu, Mathematical Foundations of the Calculus of Probability, Holden-Day 1965, Ch. V; M. I. Gordin and B. A. Lifsic, "The central limit theorem for stationary Markov processes", Soviet Math. Dokl. 19 (1978) 392-394; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.condExp_next_coord {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (h : X → ℝ) (hh : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B) (k : ℕ) :
    (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k)))
      =ᵐ[chainMeasure P lam] (chainMeasure P lam)[fun ω : ℕ → X => h (ω (k + 1)) |
        MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] := by sorry
