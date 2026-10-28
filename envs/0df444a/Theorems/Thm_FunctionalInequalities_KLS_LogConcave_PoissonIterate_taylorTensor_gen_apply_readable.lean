-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorTensor_gen_apply_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:26.075462+00:00
-- url     : https://prove2.me/theorems/f4cc32ce-29c2-4586-b75f-f09fd183f1c1
-- title:
--   Coordinate Taylor Tensor Generator Identity
-- statement:
--   This formalizes BKL Lemma 3.6 in coordinates.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U\in C^2$, and assume all exponential moments of $\nu$ are integrable. Let $u$ lie in the domain of $A=\bar T^\dagger\bar T$. For $d\in\mathbb N$ and an index map $i:\mathrm{Fin}(d+1)\to\mathrm{Fin}(\dim V)$, write $e_j$ for the standard orthonormal basis. Then the $(d+1)$st Taylor tensor of $Au$ satisfies
--
--   $$T_{d+1}(Au)(e_{i_0},\ldots,e_{i_d})
--   =\frac1{(d+1)!}\sum_{\tau\in\operatorname{Perm}(d+1)}T_d(\partial_{i_{\tau(d)}}u)(e_{i_{\tau(0)}},\ldots,e_{i_{\tau(d-1)}}).$$
--
--   The sum averages over all permutations of the $d+1$ coordinate positions.
--
--   This coordinate identity is the tensor form of the generator–gradient tilt identity and is reused in the Poisson-iterate Taylor estimates.
--
--   **Formalization Note:** Taylor tensors are formed from $L^2(\nu)$ representatives, and the coordinate indices use `Fin (Module.finrank ℝ V)`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorTensor_gen_apply {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain)
--       (d : ℕ) (i : Fin (d + 1) → Fin (Module.finrank ℝ V)) :
--       taylorTensor (ν : Measure V) (⇑(gen T̄ u)) (d + 1) (fun p => stdOrthonormalBasis ℝ V (i p)) =
--         ((d + 1).factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin (d + 1)),
--           taylorTensor (ν : Measure V) (⇑(partialDeriv T̄ (i (τ (Fin.last d))) u)) d
--             (fun p => stdOrthonormalBasis ℝ V (i (τ (Fin.castSucc p))))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Taylor`](https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`contDiff_tiltAverage_of_memLp`](https://prove2.me/theorems/48443cd3-183a-49bc-b5a9-dc2888cd75a0), [`integrable_expTilt_of_memLp`](https://prove2.me/theorems/92338882-be7b-4eaa-bd08-2e7a5b6bd38c), [`taylorTensor_succ_of_eq_inner`](https://prove2.me/theorems/93f25a59-9d8a-4033-a79b-2ccbead0cd07), [`tiltAverage_adjointComp_eq`](https://prove2.me/theorems/7fe24b66-7194-4dbb-bf46-4b6ea812f082).
--
--   Previous: [`symmetrize_apply_comp_cast`](https://prove2.me/theorems/f3dc6e21-450b-4d16-aab4-8e4451661aaa) · Next: [`symmetrize_taylorField_grad0_step`](https://prove2.me/theorems/1a522d0e-cd67-4d05-8329-16d2b2b836aa).
--
--   [Source excerpt, lines 254–259](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L254-L259) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L250-L270 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hexp

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply_readable {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain)
    (d : ℕ) (i : Fin (d + 1) → Fin (Module.finrank ℝ V)) :
    taylorTensor (ν : Measure V) (⇑(gen T̄ u)) (d + 1) (fun p => stdOrthonormalBasis ℝ V (i p)) =
      ((d + 1).factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin (d + 1)),
        taylorTensor (ν : Measure V) (⇑(partialDeriv T̄ (i (τ (Fin.last d))) u)) d
          (fun p => stdOrthonormalBasis ℝ V (i (τ (Fin.castSucc p)))) := by sorry
