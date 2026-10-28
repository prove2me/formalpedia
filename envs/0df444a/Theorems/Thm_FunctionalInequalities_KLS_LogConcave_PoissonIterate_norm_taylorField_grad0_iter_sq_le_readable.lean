-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_norm_taylorField_grad0_iter_sq_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_grad0_iter_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:49.360388+00:00
-- url     : https://prove2.me/theorems/d70ec743-efb5-4716-8d35-79b1b1891737
-- title:
--   Taylor-Field Recursion With Explicit Constants
-- statement:
--   Let $V$ be a finite-dimensional real inner-product space with the stated complete, measurable, Borel, and second-countable structures. Let $\nu$ be a log-concave probability measure on $V$, let $m$ be an additive Haar measure, and assume that the interior of the support of $\nu$ is nonempty. Let $U:V\to\mathbb R$ have temperate growth, assume
--   $$\nu=m.\operatorname{tilted}(-U),$$
--   and assume that every exponential moment $\int e^{r\|x\|}\,d\nu(x)$ is integrable. Let $C$ be a nonnegative-real parameter satisfying $C_P(\nu)\le C$ and $0<C$.
--
--   Assume the Taylor bound that, for every $u\in L^2(\nu)$ and every integer $d\ge1$,
--   $$\|T_d u\|\le R^d\|u\|,$$
--   where `taylorField` and the coordinate tensor are taken in the standard orthonormal basis. Let $f\in L^2(\nu)$ lie in the domain of the adjoint composition of the closed weighted gradient. For integers $k,d$, assume $d\ge1$, $2d\le k+1$, and, for every $j<k$,
--   $$0<\alpha_j\quad\text{and}\quad \alpha_j^2\le\frac{\beta}{C},$$
--   where $\alpha_j$ is the corresponding `scale` of the Poisson iterate.
--
--   Then, with `defect` denoting the iterate defect,
--   $$\begin{aligned}
--   \|T_d(\nabla_0 h_{k+1})\|^2
--   &\le \left(\frac{2^{20}\max(1,\beta)^2}{C}\right)^d
--      \|T_{2d}(\nabla_0 h_{k+1-d})\|^2\\
--   &\quad +(2^{20}\max(1,\beta)^2)^d R^{2d}C
--      \sum_{j\in[k+1-2d,k)}\chi_{j+1}.
--   \end{aligned}$$
--
--   This is a technical recursive estimate used to control Taylor fields of Poisson iterates and to feed the later Taylor-coefficient criterion. The explicit constant is part of the statement, rather than an unspecified universal constant.
--
--   **Formalization Note.** The Poincaré constant is compared with the coercion of a `NNReal` into $\mathbb R$; the displayed inequalities are real-valued. The sum is over `Finset.Ico`, and the indices and iterates are those represented by `taylorField`, `grad0`, `iter`, `scale`, and `defect`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_taylorField_grad0_iter_sq_le (hCpos : 0 < C) {R : ℝ}
--       (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
--         ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
--           R ^ d * ‖u‖)
--       {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) {β : ℝ} (k d : ℕ)
--       (hd : 1 ≤ d) (hdk : 2 * d ≤ k + 1)
--       (hα : ∀ j < k, 0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) :
--       ‖taylorField d (grad0 T̄ (iter T̄ f k))‖ ^ 2 ≤
--         (2 ^ 20 * max 1 β ^ 2 / C) ^ d *
--             ‖taylorField (2 * d) (grad0 T̄ (iter T̄ f (k - d)))‖ ^ 2 +
--           (2 ^ 20 * max 1 β ^ 2) ^ d * R ^ (2 * d) * C *
--             ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, defect T̄ (iter T̄ f j)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/TaylorRecursion`](https://prove2.me/theorems/bcd328b5-2d4f-467f-9a61-fa515af4f15b).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`contDiff_tiltAverage_of_memLp`](https://prove2.me/theorems/48443cd3-183a-49bc-b5a9-dc2888cd75a0), [`iteratedFDeriv_comp_perm_of_contDiff`](https://prove2.me/theorems/62e73549-6b73-43c8-a852-062236b36219), [`taylorTensor_add`](https://prove2.me/theorems/2ed3b61d-3daf-4e91-b963-da93092fcaf2), [`taylorTensor_const_mul`](https://prove2.me/theorems/7da0a874-3260-449d-b383-221740a01959), [`norm_le_four_pow_mul_norm_symmetrize`](https://prove2.me/theorems/f0e3d670-24f7-4ef8-927b-cc5e41de1898).
--
--   Previous: [`norm_symmetrize_taylorField_grad0_iter_sq_le`](https://prove2.me/theorems/de3c1c47-ae18-4799-bd2e-86a2b7358227).
--
--   [Source excerpt, lines 479–490](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/TaylorRecursion.lean#L479-L490) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma 3.8 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 15, in its route form.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 3.8, p. 15. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/TaylorRecursion.lean#L474-L577 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_grad0_iter_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion

open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
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

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_grad0_iter_sq_le_readable (hCpos : 0 < C) {R : ℝ}
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) {β : ℝ} (k d : ℕ)
    (hd : 1 ≤ d) (hdk : 2 * d ≤ k + 1)
    (hα : ∀ j < k, 0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) :
    ‖taylorField d (grad0 T̄ (iter T̄ f k))‖ ^ 2 ≤
      (2 ^ 20 * max 1 β ^ 2 / C) ^ d *
          ‖taylorField (2 * d) (grad0 T̄ (iter T̄ f (k - d)))‖ ^ 2 +
        (2 ^ 20 * max 1 β ^ 2) ^ d * R ^ (2 * d) * C *
          ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, defect T̄ (iter T̄ f j) := by sorry
