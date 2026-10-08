-- Prove2me | Theorems.Thm_MonteCarloBound_LowerBound_theorem1_lower_bound
-- name    : MonteCarloBound.LowerBound.theorem1_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:58.356573+00:00
-- url     : https://prove2.me/theorems/85039a01-3270-4994-8f32-3aae51360e2b
-- title:
--   Theorem 1, p. 49 — E z*_n ≤ z*
-- statement:
--   Consider the stochastic program
--   $$
--   z^*=\min_{x\in X} Ef(x,\tilde\xi),
--   $$
--   where $X\subseteq\mathbb R^d$ is an arbitrary feasible set (not necessarily convex, closed or bounded), $f$ is real valued, and $\tilde\xi$ is a random vector with distribution $\mu$. Assume that $Ef(x,\tilde\xi)$ exists (is finite) for every $x\in X$ and that the minimum is attained at some $x^*\in X$. Let $\tilde\xi^1,\dots,\tilde\xi^n$, $n\ge1$, be i.i.d. from the distribution of $\tilde\xi$, and let
--   $$
--   z_n^*=\min_{x\in X}\frac1n\sum_{i=1}^n f(x,\tilde\xi^i)
--   $$
--   be the optimal value of the sample-average problem $\mathrm{SP}_n$. Assume that $\mathrm{SP}_n$ is bounded below almost surely and that $Ez_n^*$ exists. Then
--   $$
--   Ez_n^*=E\min_{x\in X}\left[\frac1n\sum_{i=1}^n f(x,\tilde\xi^i)\right]\le z^*.
--   $$
--
--   The sample-average optimal value is therefore a statistical lower bound on the true optimal value, whatever the structure of $X$ and of $f(\cdot,\tilde\xi)$. It is the basis of the paper's confidence intervals on the optimality gap of a candidate solution.
--
--   **Formalization Note.** The sample is the first $n$ terms `ξ 0, …, ξ (n-1)` of an i.i.d. sequence on a probability space $(\Omega,P)$; $Ez_n^*$ is the Bochner integral over $P$, and its integrability is assumed, because a non-integrable function has integral $0$ in Lean. The paper's minima are infima (`sInf`); the attainment hypothesis on $\mathrm{SP}$ (the paper's $x^*\in\arg\min$) and the almost-sure boundedness of $\mathrm{SP}_n$ keep both infima genuine (the latter is implied by the paper's $x_n^*\in\arg\min$). The paper's standing assumption also asks for second moments of $f(x,\tilde\xi)$; they are not needed and are omitted, which makes the statement stronger. $n\ge1$ because the empty sample mean is $0$ in Lean.
-- source:
--   Mak, Morton & Wood, Oper. Res. Lett. 24 (1999), p. 49, Theorem 1; standing assumption p. 48

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting
import Definitions.Def_MonteCarloBound_LowerBound_Setting

namespace MonteCarloBound.LowerBound

open MeasureTheory ProbabilityTheory SolutionQuality.SRP

/-- Theorem 1 (p. 49): `E z*_n ≤ z*`. -/
theorem theorem1_lower_bound {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (X : Set (E d))
    (hint : ∀ x ∈ X, Integrable (f x) μ)
    (hopt : ∃ xs ∈ X, ∀ y ∈ X, expectedCost μ f xs ≤ expectedCost μ f y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (n : ℕ) (hn : 1 ≤ n)
    (hbdd : ∀ᵐ ω ∂P, BddBelow ((fun x => sampleMean f (fun i => ξ i ω) n x) '' X))
    (hzint : Integrable (fun ω => saaValue f X (fun i => ξ i ω) n) P) :
    ∫ ω, saaValue f X (fun i => ξ i ω) n ∂P ≤ optValue μ f X := by sorry

end MonteCarloBound.LowerBound
