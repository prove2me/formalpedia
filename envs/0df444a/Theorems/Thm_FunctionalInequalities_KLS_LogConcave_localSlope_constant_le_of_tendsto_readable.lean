-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_localSlope_constant_le_of_tendsto_readable
-- name    : FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_of_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:09.083171+00:00
-- url     : https://prove2.me/theorems/852c3521-f23b-43e1-9699-f0b0a407095d
-- title:
--   Literature Poincaré Bound at a Log-Concave Weak Limit
-- statement:
--   This formalizes the weak-limit transfer step of the regular-approximation reduction associated with Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered).
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure and a second-countable topology. Assume:
--
--   1. Probability measures $\mu_j$ converge weakly to a log-concave probability measure $\mu$ (`KLS.LogConcave`).
--   2. $C_j,C\in[0,\infty)$ and $C_j\to C$.
--   3. Each $\mu_j$ satisfies `Poincare.SmoothTest.Holds` with real constant $C_j$: every admissible smooth test satisfies $\operatorname{Var}_{\mu_j}(f)\le C_j\int\|\nabla f\|^2\,d\mu_j$. Admissibility requires $f\in C^\infty\cap L^2(\mu_j)$ and integrable squared gradient.
--
--   Then the intrinsic literature local-slope constant satisfies
--   $$
--   C_P^{\mathrm{lit}}(\mu)\le C.
--   $$
--   This transfers supplied smooth-test bounds to the literature constant of the limit; the approximating laws need not be log-concave.
--
--   **Formalization Note** $C_P^{\mathrm{lit}}$ is `Poincare.LocalSlope.Intrinsic.constant`, valued in `ENNReal`. The constants are `NNReal`, coerced to reals in the hypotheses and to `ENNReal` in the conclusion.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem localSlope_constant_le_of_tendsto (μs : ℕ → ProbabilityMeasure E)
--       (μ : ProbabilityMeasure E) (hμ : LogConcave μ) (Cseq : ℕ → NNReal) (C : NNReal)
--       (hlim : Tendsto μs atTop (𝓝 μ)) (hClim : Tendsto Cseq atTop (𝓝 C))
--       (hbound : ∀ j, Poincare.SmoothTest.Holds (μs j : Measure E) (Cseq j : ℝ)) :
--       Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeakLimit`](https://prove2.me/theorems/7f87bac4-42a8-4711-b788-2d3b139d7914).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1), [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   Selected supporting theorems: [`exists_ambient_extension`](https://prove2.me/theorems/eca5f601-3244-4c7a-abb0-b647df83122f), [`Admissible.of_contDiff_hasCompactSupport`](https://prove2.me/theorems/7f79ab39-6c03-4d68-870d-2dd02d1e1b0b), [`Holds.of_compactSupport`](https://prove2.me/theorems/7a878356-8017-4c9f-ae31-615b3aebf1ac), [`holds_iff_localSlope`](https://prove2.me/theorems/80f4b23b-124c-49c3-a604-c5a3355c1bc0), [`variance_le_mul_energy_of_tendsto`](https://prove2.me/theorems/0405b112-362b-4b97-b8df-8b73697c57e3).
--
--   [Source excerpt, lines 28–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeakLimit.lean#L28-L32) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeakLimit.lean#L21-L44 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeakLimit`, declaration `FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_of_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeakLimit

open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_of_tendsto_readable (μs : ℕ → ProbabilityMeasure E)
    (μ : ProbabilityMeasure E) (hμ : LogConcave μ) (Cseq : ℕ → NNReal) (C : NNReal)
    (hlim : Tendsto μs atTop (𝓝 μ)) (hClim : Tendsto Cseq atTop (𝓝 C))
    (hbound : ∀ j, Poincare.SmoothTest.Holds (μs j : Measure E) (Cseq j : ℝ)) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) := by sorry
