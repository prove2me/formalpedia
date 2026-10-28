-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_norm_symmetrize_taylorField_grad0_iter_sq_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:02.624763+00:00
-- url     : https://prove2.me/theorems/de3c1c47-ae18-4799-bd2e-86a2b7358227
-- title:
--   Iterated Taylor Symmetrization Bound
-- statement:
--   This formalizes BKL (56)–(57).
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U$ of temperate growth and all exponential moments, and assume $C_P(\nu)\le C$. For $f\in L^2(\nu)$, let $e,d,k\in\mathbb N$ satisfy $d\ge1$ and $e\le k$. Suppose that for every $j<k$,
--
--   $$\alpha_j^2\le\frac\beta C,$$
--
--   where $\alpha_j$ is the scale of the $j$th Poisson iterate. Then
--
--   $$\left\|S_{d+e}T_d(\nabla_0h_{k+1})\right\|^2
--   \le\left(\frac\beta C\right)^e
--   \left\|T_{d+e}(\nabla_0h_{k+1-e})\right\|^2.$$
--
--   Here $S_{d+e}$ symmetrizes the indicated initial positions and the Taylor fields are represented by the formalization's `taylorField`.
--
--   This estimate iterates the one-step Taylor-field identity and supplies the main recursive contraction factor.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_symmetrize_taylorField_grad0_iter_sq_le (f : Lp ℝ 2 (ν : Measure V)) {β : ℝ}
--       (e : ℕ) : ∀ (d k : ℕ), 1 ≤ d → e ≤ k → (∀ j < k, scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
--         ‖symmetrize (Module.finrank ℝ V) (d + (k + 1)) (d + e)
--             (taylorField d (grad0 T̄ (iter T̄ f k)))‖ ^ 2 ≤
--           (β / C) ^ e * ‖taylorField (d + e) (grad0 T̄ (iter T̄ f (k - e)))‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/TaylorRecursion`](https://prove2.me/theorems/bcd328b5-2d4f-467f-9a61-fa515af4f15b).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`symmetrize_taylorField_grad0_step`](https://prove2.me/theorems/1a522d0e-cd67-4d05-8329-16d2b2b836aa).
--
--   Next: [`norm_taylorField_grad0_iter_sq_le`](https://prove2.me/theorems/d70ec743-efb5-4716-8d35-79b1b1891737).
--
--   [Source excerpt, lines 435–439](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/TaylorRecursion.lean#L435-L439) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/TaylorRecursion.lean#L432-L472 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion

open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hUt hexp hC

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le_readable (f : Lp ℝ 2 (ν : Measure V)) {β : ℝ}
    (e : ℕ) : ∀ (d k : ℕ), 1 ≤ d → e ≤ k → (∀ j < k, scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      ‖symmetrize (Module.finrank ℝ V) (d + (k + 1)) (d + e)
          (taylorField d (grad0 T̄ (iter T̄ f k)))‖ ^ 2 ≤
        (β / C) ^ e * ‖taylorField (d + e) (grad0 T̄ (iter T̄ f (k - e)))‖ ^ 2 := by sorry
