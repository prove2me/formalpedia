-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_32
-- name    : OCEClocks.DisplayAds.lemma_32
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:23:10.050988+00:00
-- url     : https://prove2.me/theorems/4f0d180a-f697-4021-8fd1-0eae1365cd76
-- title:
--   Lemma 32 — explicit formula for the matching kernel $M_x$
-- statement:
--   Let $\lambda>0$, $0<x<1$, $a\ge0$, and let $f$ be a bounded measurable function on ages. With $D_x$ as in Lemma 29, the matching kernel (4) satisfies
--
--   $$(M_xf)(a)=\big(e^{-\lambda x}-xe^{-\lambda}\big)f(a+x)+\int_0^x\lambda e^{-\lambda s}\big(1-D_x(a+s)\big)\Big(e^{-\lambda(x-s)}f(x-s)+\int_0^{x-s}\lambda e^{-\lambda v}f(v)\,dv\Big)\,ds.$$
--
--   The formula separates the event of no arrival during the request from the first arrival at time $s$. It is the starting point of the generator computation (Lemma 10) and of the certified bounds behind Lemma 18.
--
--   **Formalization Note** $f:\mathbb R\to\mathbb R$ is measurable and bounded on $[0,\infty)$; only its values at ages are used. The integrals are interval integrals over $(0,x)$ and $(0,x-s)$.
--
--   Differences from the source:
--   - generalization: λ = 4.5 ("The rest of the paper fixes λ = 4.5", p. 9) → every λ > 0; reason: the printed statement does not depend on the value of λ; at λ = 9/2 the Lean statement is the paper's
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
--   - encoding: measures and functions on ages [0, ∞) → finite measures on ℝ and functions ℝ → ℝ; only ages a ≥ 0 occur, and boundedness/regularity hypotheses are imposed on [0, ∞) only; reason: Lean convention; same instances
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 38, Lemma 32

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Kernels

namespace OCEClocks.DisplayAds

/-- Lemma 32 (p. 38): the explicit formula for the matching kernel `(M_x f)(a)`, for every bounded
measurable function `f` on ages, every age `a ≥ 0` and every request `0 < x < 1`. -/
theorem lemma_32 (lam : ℝ) (hlam : 0 < lam) (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ b : ℝ, 0 ≤ b → |f b| ≤ C) (a : ℝ) (ha : 0 ≤ a) (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    matchingKernel lam x f a =
      (Real.exp (-(lam * x)) - x * Real.exp (-lam)) * f (a + x) +
        ∫ s in (0 : ℝ)..x, lam * Real.exp (-(lam * s)) * (1 - winProbGivenAge lam x (a + s)) *
          (Real.exp (-(lam * (x - s))) * f (x - s) +
            ∫ v in (0 : ℝ)..(x - s), lam * Real.exp (-(lam * v)) * f v) := by sorry

end OCEClocks.DisplayAds
