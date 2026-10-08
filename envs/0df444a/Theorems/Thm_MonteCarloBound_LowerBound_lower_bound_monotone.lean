-- Prove2me | Theorems.Thm_MonteCarloBound_LowerBound_lower_bound_monotone
-- name    : MonteCarloBound.LowerBound.lower_bound_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:21.36368+00:00
-- url     : https://prove2.me/theorems/ab6cde64-e5f4-439f-b99e-0ddb06c9bea8
-- title:
--   Introduction, p. 48 (Theorems 1–2) — E z*_n ≤ E z*_{n+1} ≤ z*
-- statement:
--   Consider the stochastic program and its sample-average approximation
--   $$
--   z^*=\min_{x\in X} Ef(x,\tilde\xi),\qquad z_n^*=\min_{x\in X}\frac1n\sum_{i=1}^n f(x,\tilde\xi^i),
--   $$
--   where $X\subseteq\mathbb R^d$ is an arbitrary feasible set, $f$ is real valued, $\tilde\xi$ has distribution $\mu$, and $\tilde\xi^1,\tilde\xi^2,\dots$ are i.i.d. from the distribution of $\tilde\xi$ (the same sequence defines every $z_m^*$). Assume:
--
--   1. $Ef(x,\tilde\xi)$ exists for every $x\in X$, and $\mathrm{SP}$ has an optimal solution $x^*\in X$;
--   2. with probability one, every $\mathrm{SP}_m$, $m\ge1$, has an optimal solution $x_m^*$;
--   3. $Ez_n^*$ and $Ez_{n+1}^*$ exist, and $z_n^*$ is a random variable (measurable as a function of the sample path).
--
--   Then, for every $n\ge1$,
--   $$
--   Ez_n^*\ \le\ Ez_{n+1}^*\ \le\ z^*.
--   $$
--
--   Thus $z_n^*$ is a probabilistic lower bound on $z^*$ that improves, in expectation, with increasing sample size. This is the paper's headline result, the conjunction of Theorem 2 at $n$ and Theorem 1 at $n+1$.
--
--   **Formalization Note.** The sample is one infinite i.i.d. sequence `ξ 0, ξ 1, …` on a probability space $(\Omega,P)$; $z_m^*$ uses its first $m$ terms. Minima are infima (`sInf`); hypotheses 1 and 2 are the paper's "$x^*\in\arg\min$" and "$x_n^*\in\arg\min$" and keep them genuine. Hypothesis 2 is stated almost surely for the law of the sample path. Expectations are Bochner integrals, and the integrability in hypothesis 3 makes "$Ez_m^*$ exists" precise. The standing assumption's second moments are not needed and are omitted.
-- source:
--   Mak, Morton & Wood, Oper. Res. Lett. 24 (1999), p. 48, Introduction; p. 49, Theorem 1; p. 50, Theorem 2

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting
import Definitions.Def_MonteCarloBound_LowerBound_Setting

namespace MonteCarloBound.LowerBound

open MeasureTheory ProbabilityTheory SolutionQuality.SRP

/-- Introduction (p. 48), Theorems 1–2: `E z*_n ≤ E z*_{n+1} ≤ z*`. -/
theorem lower_bound_monotone {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (X : Set (E d))
    (hint : ∀ x ∈ X, Integrable (f x) μ)
    (hopt : ∃ xs ∈ X, ∀ y ∈ X, expectedCost μ f xs ≤ expectedCost μ f y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (n : ℕ) (hn : 1 ≤ n)
    (hmin : ∀ᵐ s ∂(pathLaw P ξ), ∀ m, 1 ≤ m →
      ∃ x ∈ X, ∀ y ∈ X, sampleMean f s m x ≤ sampleMean f s m y)
    (hzint : Integrable (fun ω => saaValue f X (fun i => ξ i ω) n) P)
    (hzint1 : Integrable (fun ω => saaValue f X (fun i => ξ i ω) (n + 1)) P)
    (hzmeas : Measurable (fun s : ℕ → Ξ => saaValue f X s n)) :
    (∫ ω, saaValue f X (fun i => ξ i ω) n ∂P ≤
        ∫ ω, saaValue f X (fun i => ξ i ω) (n + 1) ∂P) ∧
      ∫ ω, saaValue f X (fun i => ξ i ω) (n + 1) ∂P ≤ optValue μ f X := by sorry

end MonteCarloBound.LowerBound
