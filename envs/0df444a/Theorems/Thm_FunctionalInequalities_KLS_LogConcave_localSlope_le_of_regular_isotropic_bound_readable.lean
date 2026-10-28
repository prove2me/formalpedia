-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_localSlope_le_of_regular_isotropic_bound_readable
-- name    : FunctionalInequalities.KLS.LogConcave.localSlope_le_of_regular_isotropic_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:57.32128+00:00
-- url     : https://prove2.me/theorems/621a2407-818c-46e6-9957-c61bcf6e344e
-- title:
--   Conditional Reduction From Isotropic Log-Concave Laws to Regular Laws
-- statement:
--   This is a conditional reduction of an isotropic log-concave Poincaré bound to a bound on isotropic regular laws in the same space.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure, and fix $K\in[0,\infty)$. Assume that for every $V:E\to\mathbb R$, $a,b\in\mathbb R$, and $h_V:$ `KLS.RegularPotential V a b`,
--   $$
--   b>0\ \text{ and }\ \operatorname{Isotropic}(\operatorname{law}(h_V))
--   \quad\Longrightarrow\quad
--   C_P^{\mathrm{lit}}(\operatorname{law}(h_V))\le K.
--   $$
--   Then every probability measure $\mu$ on $E$ that is both log-concave (`KLS.LogConcave`) and isotropic (`KLS.Isotropic`) satisfies
--   $$
--   C_P^{\mathrm{lit}}(\mu)\le K.
--   $$
--   Isotropy requires finite second moment, zero mean, and identity centered covariance. The law in the hypothesis is `RegularPotential.law`; $C_P^{\mathrm{lit}}$ is `Poincare.LocalSlope.Intrinsic.constant`.
--
--   This reduction preserves a supplied bound $K$; it does not establish the regular-law hypothesis or the existence of such a bound.
--
--   **Formalization Note** $K$ is `NNReal`, and both inequalities use its coercion to `ENNReal`. The statement concerns one fixed space $E$ and includes dimension zero.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem localSlope_le_of_regular_isotropic_bound {K : NNReal}
--       (hBound : ∀ {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b),
--         0 < b → KLS.Isotropic hV.law →
--           Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (K : ENNReal))
--       (μ : ProbabilityMeasure E) (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
--       Poincare.LocalSlope.Intrinsic.constant μ ≤ (K : ENNReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/IsotropicReduction`](https://prove2.me/theorems/71545edb-cd76-4fa7-a5a9-f3cfaa7db601).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`exists_metric_diagonal`](https://prove2.me/theorems/c1baf226-693c-4f22-b2f1-ccc4640d1cd9), [`relaxation_eq_ofLinearPMap`](https://prove2.me/theorems/ecd8db80-1079-4c3b-8976-dc3390ed944f), [`relaxation_le_mul_lipschitz`](https://prove2.me/theorems/62ed0b65-a0a8-46f7-b7c9-4f855a09ceaf), [`relaxation_mapContinuousLinearEquiv`](https://prove2.me/theorems/57355011-3577-4382-8bb8-e203da4929a1).
--
--   [Source excerpt, lines 60–65](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/IsotropicReduction.lean#L60-L65) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/IsotropicReduction.lean#L56-L95 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.IsotropicReduction`, declaration `FunctionalInequalities.KLS.LogConcave.localSlope_le_of_regular_isotropic_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction

open MeasureTheory Filter Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.localSlope_le_of_regular_isotropic_bound_readable {K : NNReal}
    (hBound : ∀ {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b),
      0 < b → KLS.Isotropic hV.law →
        Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (K : ENNReal))
    (μ : ProbabilityMeasure E) (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (K : ENNReal) := by sorry
