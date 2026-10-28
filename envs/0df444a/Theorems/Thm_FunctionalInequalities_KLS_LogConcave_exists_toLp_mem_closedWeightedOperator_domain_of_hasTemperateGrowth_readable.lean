-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:03.224864+00:00
-- url     : https://prove2.me/theorems/de152049-2180-4f95-9606-5806b95406d7
-- title:
--   Temperate Functions Belong To The Closed Gradient Domain
-- statement:
--   This is a classical-to-$L^2$ domain bridge for the closed weighted gradient.
--
--   Let $V$ be a finite-dimensional real inner-product space with the stated topological and measurable structures. Let $\nu$ be log-concave, let $m$ be an additive Haar measure, and assume that the interior of the support of $\nu$ is nonempty. Assume every exponential moment of $\nu$ is integrable. For every function $f:V\to\mathbb R$ of temperate growth, there exist
--   1. a proof that $f\in L^2(\nu)$;
--   2. a proof that its gradient $\nabla f\in L^2(\nu)$; and
--   3. a proof that the $L^2$ class of $f$ lies in the domain of the closed weighted operator.
--
--   If these objects are denoted by $[f]$ and $[\nabla f]$, then
--   $$\overline{\nabla}[f]=[\nabla f].$$
--
--   This result supplies operator-domain membership for temperate test functions and is useful for transferring classical differential identities to $L^2$ classes.
--
--   **Formalization Note.** The witnesses are `MemLp` proofs and a domain-membership proof; `toLp` denotes the corresponding $L^2(\nu)$ representatives.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth {f : V → ℝ}
--       (hf : f.HasTemperateGrowth) :
--       ∃ (hf2 : MemLp f 2 (ν : Measure V)) (hg2 : MemLp (gradient f) 2 (ν : Measure V))
--         (hmem : hf2.toLp f ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
--         hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem⟩ = hg2.toLp (gradient f)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Temperate`](https://prove2.me/theorems/1eb5f917-f4b3-485c-b451-be82d396cded).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`cutoff_eq_one`](https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec), [`hasCompactSupport_cutoff`](https://prove2.me/theorems/d329d169-7e19-4110-aeb8-20df20dddcfb), [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db), [`norm_iteratedFDeriv_cutoff_le`](https://prove2.me/theorems/d1de012f-6a55-4617-aaf5-23eabb181c3e).
--
--   [Source excerpt, lines 124–128](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Temperate.lean#L124-L128) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Temperate.lean#L121-L221 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Temperate`, declaration `FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Temperate

open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
include hexp

theorem FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth_readable {f : V → ℝ}
    (hf : f.HasTemperateGrowth) :
    ∃ (hf2 : MemLp f 2 (ν : Measure V)) (hg2 : MemLp (gradient f) 2 (ν : Measure V))
      (hmem : hf2.toLp f ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem⟩ = hg2.toLp (gradient f) := by sorry
