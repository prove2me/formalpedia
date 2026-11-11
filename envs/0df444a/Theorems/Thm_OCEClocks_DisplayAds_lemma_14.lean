-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_14
-- name    : OCEClocks.DisplayAds.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:23:07.319183+00:00
-- url     : https://prove2.me/theorems/f95243f5-f567-4682-b5d5-0e871f2a32c0
-- title:
--   Lemma 14 — infinitesimal generator $L_Gf=f'-\lambda f+\lambda f(0)$ of the gap kernel
-- statement:
--   Let $\lambda>0$ and let $G_t$ be the gap kernel, $(G_tf)(a)=\mathbb E[f(A(t))\mid A(0)=a]$, for the age process that grows at unit rate and resets to $0$ at rate-$\lambda$ Poisson arrivals. Let $f$ be a bounded, continuously differentiable function on ages with bounded derivative $f'$, where the derivative at $0$ is the right derivative. Then for every age $a\ge0$,
--
--   $$(L_Gf)(a):=\lim_{t\downarrow0}\frac{(G_tf)(a)-f(a)}{t}=f'(a)-\lambda f(a)+\lambda f(0).$$
--
--   This generator, with the ODE of Lemma 31, drives the derivative bound of Lemma 19 through the Kolmogorov equation.
--
--   **Formalization Note** The hypotheses are imposed on $[0,\infty)$: $f$ and $f'$ are bounded there, $f'$ is continuous there, and $f$ has derivative $f'(b)$ within $[0,\infty)$ at every $b\ge0$ (the right derivative at $0$). The conclusion asserts that the right limit of the difference quotient exists and equals the stated value; $L_G$ is defined as this limit, like $L_M$ on p. 11.
--
--   Differences from the source:
--   - generalization: λ = 4.5 ("The rest of the paper fixes λ = 4.5", p. 9) → every λ > 0; reason: the printed statement does not depend on the value of λ; at λ = 9/2 the Lean statement is the paper's
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
--   - encoding: measures and functions on ages [0, ∞) → finite measures on ℝ and functions ℝ → ℝ; only ages a ≥ 0 occur, and boundedness/regularity hypotheses are imposed on [0, ∞) only; reason: Lean convention; same instances
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 15, Lemma 14

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Kernels

open Filter Topology

namespace OCEClocks.DisplayAds

/-- Lemma 14 (p. 15): the infinitesimal generator of the gap kernel,
`(L_G f)(a) = lim_{t ↓ 0} ((G_t f)(a) - f(a)) / t = f'(a) - λ f(a) + λ f(0)`, for every bounded
continuously differentiable `f` on ages with bounded derivative (right derivative at `0`). -/
theorem lemma_14 (lam : ℝ) (hlam : 0 < lam) (f f' : ℝ → ℝ)
    (hf : ∃ C : ℝ, ∀ b : ℝ, 0 ≤ b → |f b| ≤ C) (hf' : ∃ C : ℝ, ∀ b : ℝ, 0 ≤ b → |f' b| ≤ C)
    (hderiv : ∀ b : ℝ, 0 ≤ b → HasDerivWithinAt f (f' b) (Set.Ici 0) b)
    (hcont : ContinuousOn f' (Set.Ici 0)) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun t => (gapKernel lam t f a - f a) / t) (𝓝[>] 0)
      (𝓝 (f' a - lam * f a + lam * f 0)) := by sorry

end OCEClocks.DisplayAds
