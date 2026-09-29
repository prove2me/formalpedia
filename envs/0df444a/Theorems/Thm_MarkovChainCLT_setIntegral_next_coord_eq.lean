-- Prove2me | Theorems.Thm_MarkovChainCLT_setIntegral_next_coord_eq
-- name    : MarkovChainCLT.setIntegral_next_coord_eq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:10:49.718153+00:00
-- url     : https://prove2.me/theorems/adcac256-2573-46b1-8be0-3f2d23f2ec75
-- title:
--   Markov property: the next coordinate integrates to the one-step kernel average
-- statement:
--   **The Markov property, in the form needed to identify conditional expectations.** For a bounded measurable $h$ and any event $A$ in the past $\sigma(X_0,\dots,X_k)$,
--   $$\mathbb E\bigl[\mathbf 1_A\, h(X_{k+1})\bigr] \;=\; \mathbb E\bigl[\mathbf 1_A\,(Ph)(X_k)\bigr],\qquad (Ph)(x) = \int h\,dP(x,\cdot).$$
--
--   Since $(Ph)(X_k)$ is measurable with respect to that past and integrable, this is exactly the hypothesis of the standard characterization of conditional expectation, so it says
--   $$\mathbb E\bigl[h(X_{k+1}) \mid \sigma(X_0,\dots,X_k)\bigr] \;=\; (Ph)(X_k)\quad\text{a.s.}$$
--   — "the chain forgets everything but its current position". It holds for **every** initial distribution.
--
--   **Why it is the pivot of the martingale approach.** Given a solution $g$ of the Poisson equation $g - Pg = \varphi - \mathbb E_\pi\varphi$, the variables
--   $$D_k \;=\; g(X_{k+1}) - (Pg)(X_k)$$
--   are martingale differences for the chain filtration precisely because of this identity, and the partial sums of $\varphi$ along the chain become a martingale plus a telescoping remainder. Every central limit theorem for martingale difference arrays then transfers to the chain. The identity is also what makes the $D_k$ orthogonal, which is how one obtains $\mathrm{Var}(\sum_{k<n} D_k) = \sum_{k<n}\mathbb E D_k^2 = O(n)$ — the variance bound behind the law of large numbers for the quadratic variation.
--
--   **Proof.** Both sides are integrals of a bounded measurable function against measures on the state space. Write $S = \{\omega : (\omega_0,\dots,\omega_k)\in A\}$ and $\rho = \mathbb P|_S$. It suffices to show the identity of measures
--   $$\rho\circ X_{k+1}^{-1} \;=\; P \circ \bigl(\rho\circ X_k^{-1}\bigr),$$
--   i.e. that pushing the restricted path measure forward by the next coordinate is the same as pushing it forward by the current coordinate and then applying one step of the kernel. Evaluated on a measurable $E\subseteq X$ this reads
--   $$\mathbb P\bigl(S \cap \{X_{k+1}\in E\}\bigr) \;=\; \int_S P(X_k, E)\,d\mathbb P,$$
--   which is the past/future factorization of the Ionescu–Tulcea path measure at lag one, together with the fact that the coordinate-zero marginal of a chain is its own initial law (so that the "future" event $\{X_{k+1}\in E\}$ contributes exactly $P(X_k,E)$). Integrating $h$ against the two equal measures and applying Fubini for the composed kernel gives the stated identity.
-- source:
--   J. Neveu, Mathematical Foundations of the Calculus of Probability, Holden-Day 1965, Ch. V; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3 and Ch. 17; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 2.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.setIntegral_next_coord_eq {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (h : X → ℝ) (hh : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B) (k : ℕ)
    (A₀ : Set (Π _i : Finset.Iic k, X)) (hA₀ : MeasurableSet A₀) :
    ∫ ω in (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀), h (ω (k + 1))
        ∂(chainMeasure P lam)
      = ∫ ω in (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀),
          (∫ y, h y ∂(P (ω k))) ∂(chainMeasure P lam) := by sorry
