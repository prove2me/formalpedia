-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_hessianSq_add_le_of_hasTemperateGrowth_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_hessianSq_add_le_of_hasTemperateGrowth_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:08.670143+00:00
-- url     : https://prove2.me/theorems/fcac2fc2-d13a-43a7-b290-c7c1b8a429f0
-- title:
--   Integrated Bochner Curvature Inequality
-- statement:
--   This formalizes the curvature inequality associated with Equation (16) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), used in Lemma 3.4.
--
--   Let $E$ be a finite-dimensional real inner-product Banach space, let $m$ be an additive Haar measure on $E$, and let $V,f:E\to\mathbb R$. Assume:
--
--   1. $V$ has temperate growth.
--   2. For every $r\in\mathbb R$, the function $x\mapsto e^{r\|x\|}$ is integrable with respect to the tilted measure $m.\operatorname{tilted}(-V)$.
--   3. $f$ has temperate growth.
--   4. There is $\rho\in\mathbb R$ such that, for every $x,v\in E$,
--      $$\rho\|v\|^2\le D^2V(x)[v,v].$$
--
--   Then, with `hessianSqStdBasis` denoting the squared Hilbert–Schmidt norm of the Hessian and `weightedLaplacian` the weighted Laplacian,
--
--   $$\int \operatorname{hessianSqStdBasis}(f)(x)\,d\mu(x)+\rho\int\|\nabla f(x)\|^2\,d\mu(x)\le \int\bigl(\operatorname{weightedLaplacian}(V,f)(x)\bigr)^2\,d\mu(x),$$
--
--   where $\mu=m.\operatorname{tilted}(-V)$.
--
--   This is an integrated Bochner-type estimate under a pointwise Hessian lower bound and is reusable in curvature and energy arguments for temperate functions.
--
--   **Formalization Note.** All integrals are real-valued integrals against the tilted measure; the statement is finite-dimensional and uses the exact temperate-growth and exponential-integrability hypotheses shown above.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_hessianSq_add_le_of_hasTemperateGrowth {V f : E → ℝ} (hV : V.HasTemperateGrowth)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
--       (hf : f.HasTemperateGrowth) {ρ : ℝ}
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v) :
--       ∫ x, hessianSqStdBasis f x ∂(m.tilted (-V)) + ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂(m.tilted (-V)) ≤
--         ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Temperate`](https://prove2.me/theorems/3d0b9fbe-846b-4821-b768-fdcecccd6374).
--
--   Definition modules: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db), [`integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth`](https://prove2.me/theorems/60f35586-717a-4f01-a5d5-ebcf392e454c).
--
--   Previous: [`integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth`](https://prove2.me/theorems/60f35586-717a-4f01-a5d5-ebcf392e454c).
--
--   [Source excerpt, lines 227–232](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Temperate.lean#L227-L232) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (16), p. 6 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Temperate.lean#L225-L247 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_hessianSq_add_le_of_hasTemperateGrowth`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Temperate

open MeasureTheory Filter Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_hessianSq_add_le_of_hasTemperateGrowth_readable {V f : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v) :
    ∫ x, hessianSqStdBasis f x ∂(m.tilted (-V)) + ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂(m.tilted (-V)) ≤
      ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) := by sorry
