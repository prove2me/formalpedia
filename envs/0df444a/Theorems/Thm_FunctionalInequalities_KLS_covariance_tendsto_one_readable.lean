-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_covariance_tendsto_one_readable
-- name    : FunctionalInequalities.KLS.covariance_tendsto_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:37.862123+00:00
-- url     : https://prove2.me/theorems/931a2bcc-f8c0-48ee-8d9a-a38753c18c36
-- title:
--   Convergence of Covariance Operators from Low Moments
-- statement:
--   This auxiliary lemma shows convergence of covariance operators from support and moment hypotheses.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $(λ_k)$ and $μ$ be probability measures on $E$, and assume `Isotropic μ`. Fix $R\in\mathbb R$. Suppose:
--
--   1. every $λ_k$ gives measure zero to the complement of the closed ball $\overline B(0,R)$;
--   2. for every degree $d\le 4$ and every family $v:\operatorname{Fin}(d)\to E$, the mixed moments of $λ_k$ converge to those of $μ$:
--
--   $$
--   \int_E\prod_i\langle v_i,x\rangle\,dλ_k(x)
--   \longrightarrow
--   \int_E\prod_i\langle v_i,x\rangle\,dμ(x).
--   $$
--
--   Then the covariance operators converge to the identity operator:
--
--   $$
--   \operatorname{Covariance.operator}(λ_k)\longrightarrow I
--   $$
--
--   in the operator topology.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma covariance_tendsto_one
--       {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
--       (hiso : Isotropic μ) {R : ℝ}
--       (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
--       (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
--         Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
--           (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
--       Tendsto (fun k => Covariance.operator (lam k : Measure E)) atTop (𝓝 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/BallConditioning`](https://prove2.me/theorems/2fa3d0ff-8849-4ff0-b13d-3697177849fc).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Previous: [`exists_regularClass_of_cond_closedBall_map`](https://prove2.me/theorems/09f327ff-9750-431b-aefd-04c440b44d3b) · Next: [`whitening_sequence`](https://prove2.me/theorems/4f39d579-4312-46d4-8a78-c4f9ba76eab9).
--
--   [Source excerpt, lines 321–328](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L321-L328) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L321-L369 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.BallConditioning`, declaration `_private.FunctionalInequalities.KLS.LogConcave.BallConditioning.0.FunctionalInequalities.KLS.covariance_tendsto_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning

open MeasureTheory Set Metric Filter
open scoped Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

lemma FunctionalInequalities.KLS.covariance_tendsto_one_readable
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    Tendsto (fun k => Covariance.operator (lam k : Measure E)) atTop (𝓝 1) := by sorry
