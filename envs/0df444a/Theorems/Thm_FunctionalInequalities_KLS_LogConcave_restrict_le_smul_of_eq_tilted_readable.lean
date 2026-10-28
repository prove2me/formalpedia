-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_restrict_le_smul_of_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.restrict_le_smul_of_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:17.931406+00:00
-- url     : https://prove2.me/theorems/7744a7a5-331d-4220-a88d-91325cd3a0c8
-- title:
--   Compact-Set Haar Domination By A Tilted Probability Law
-- statement:
--   This theorem gives a finite measure domination on compact sets.
--
--   Let $V$ be a measurable Borel normed space, let $m$ be an additive Haar measure, let $\nu$ be a probability measure, and let $U:V\to\mathbb R$ be continuous with $\nu=m.\operatorname{tilted}(-U)$. For every compact set $K\subseteq V$, there exists $c\in[0,\infty]$ such that $c\ne\infty$ and
--
--   $$
--   m\!\restriction_K\le c\,\nu.
--   $$
--
--   Thus the restriction of Haar measure to any compact set is dominated by a finite scalar multiple of the tilted law. The result is used to obtain local integrability with respect to Haar measure from $L^2(\nu)$ information.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem restrict_le_smul_of_eq_tilted (hνU : (ν : Measure V) = m.tilted (-U)) (hU : Continuous U)
--       {K : Set V} (hK : IsCompact K) :
--       ∃ c : ENNReal, c ≠ ⊤ ∧ m.restrict K ≤ c • (ν : Measure V)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70).
--
--   Previous: [`integral_eq_integral_mul_exp`](https://prove2.me/theorems/e50ba0fe-194c-4fab-a951-2f7b7b282f0a) · Next: [`tendsto_integral_mul_of_tendsto`](https://prove2.me/theorems/0ead0018-76f8-4e4a-918c-0de12ef6b171).
--
--   [Source excerpt, lines 81–83](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L81-L83) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L77-L134 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, declaration `FunctionalInequalities.KLS.LogConcave.restrict_le_smul_of_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
omit [InnerProductSpace ℝ V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.LogConcave.restrict_le_smul_of_eq_tilted_readable (hνU : (ν : Measure V) = m.tilted (-U)) (hU : Continuous U)
    {K : Set V} (hK : IsCompact K) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ m.restrict K ≤ c • (ν : Measure V) := by sorry
