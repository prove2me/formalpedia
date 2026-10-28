-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_mem_domain_closedWeightedOperator_toLp_mul_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_mem_domain_closedWeightedOperator_toLp_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:11.821987+00:00
-- url     : https://prove2.me/theorems/465ec746-a212-4a4a-a2ab-2d9cca0a20ec
-- title:
--   Leibniz Rule For The Closed Weighted Gradient
-- statement:
--   This theorem extends the product rule to every element of the closed weighted-gradient domain.
--
--   Let $V$ be finite-dimensional with the stated structures, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $B:V\to V$ be continuous linear. For a smooth compactly supported multiplier $\phi:V\to\mathbb R$ and any
--
--   $$
--   x\in D\!\left(\overline{T}_{\nu,m,B}\right),
--   $$
--
--   there exists a proof of domain membership for the $L^2(\nu)$ class of $\phi x$, and the resulting operator value satisfies, $\nu$-almost everywhere,
--
--   $$
--   \overline{T}_{\nu,m,B}(\phi x)
--   =
--   \phi\,\overline{T}_{\nu,m,B}x+x\,(B\nabla\phi).
--   $$
--
--   The statement uses `toLp` for the product class and `closedWeightedOperator` for the closed operator. No boundedness or differentiability of $x$ is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_mem_domain_closedWeightedOperator_toLp_mul {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
--       (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain) :
--       ∃ hmem : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
--           (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain,
--         ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
--           =ᵐ[(ν : Measure V)] fun y =>
--             φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
--               + (x : Lp ℝ 2 (ν : Measure V)) y • apply B φ y
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Basic`](https://prove2.me/theorems/f6b93e94-4e8d-4cc9-94ea-458e2669b85c).
--
--   Supporting theorems: [`exists_seq_smooth_tendsto_graph`](https://prove2.me/theorems/c7be6850-4704-4912-95fa-1692fa90fd5a).
--
--   Previous: [`exists_seq_smooth_tendsto_graph`](https://prove2.me/theorems/c7be6850-4704-4912-95fa-1692fa90fd5a).
--
--   [Source excerpt, lines 134–141](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean#L134-L141) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean#L124-L230 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier`, declaration `FunctionalInequalities.KLS.LogConcave.exists_mem_domain_closedWeightedOperator_toLp_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier

open MeasureTheory Filter Topology
open scoped ContDiff
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)

theorem FunctionalInequalities.KLS.LogConcave.exists_mem_domain_closedWeightedOperator_toLp_mul_readable {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ hmem : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain,
      ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
        =ᵐ[(ν : Measure V)] fun y =>
          φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
            + (x : Lp ℝ 2 (ν : Measure V)) y • apply B φ y := by sorry
