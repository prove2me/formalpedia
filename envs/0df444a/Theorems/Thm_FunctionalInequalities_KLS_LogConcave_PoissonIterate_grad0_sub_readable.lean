-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_grad0_sub_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:23.854701+00:00
-- url     : https://prove2.me/theorems/4388ae07-53e8-4f4c-88d5-4b286c971585
-- title:
--   Additivity of the Centered Gradient
-- statement:
--   Let $T$ be a linear gradient-type partial operator, and let $u,v$ be level-$k$ fields whose components all lie in the domain of $T$. Then the centered gradient is additive:
--
--   $$\nabla_0(u-v)=\nabla_0u-\nabla_0v.$$
--
--   The equality is componentwise as a field of $L^2(\nu;V)$ classes. This is a technical linearity lemma used when comparing Poisson steps under permutations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem grad0_sub {k : ℕ} {u v : Field ν k} (hu : ∀ I, u I ∈ T.domain)
--       (hv : ∀ I, v I ∈ T.domain) : grad0 T (u - v) = grad0 T u - grad0 T v
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Symmetry`](https://prove2.me/theorems/39390486-c6df-45a6-82e9-cb779c8b05f8).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375).
--
--   Next: [`grad0_step_sub_permField_succ`](https://prove2.me/theorems/39d622b5-c0a8-4e3a-93dc-27f25675ab33).
--
--   [Source excerpt, lines 122–123](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Symmetry.lean#L122-L123) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Symmetry.lean#L121-L135 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_sub`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Symmetry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
  (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_sub_readable {k : ℕ} {u v : Field ν k} (hu : ∀ I, u I ∈ T.domain)
    (hv : ∀ I, v I ∈ T.domain) : grad0 T (u - v) = grad0 T u - grad0 T v := by sorry
