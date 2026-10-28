-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_localSlope_le_of_cumulantBound_all_readable
-- name    : FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:53.866952+00:00
-- url     : https://prove2.me/theorems/cb774c5b-d478-4527-a81e-37c436cdedf4
-- title:
--   Finite-Dimensional Poincaré Bound from Universal Cumulant Bounds
-- statement:
--   This formalizes the conditional form of Theorem 1.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 2.
--
--   There exists a real constant $C>0$ such that, for every $K\in\mathbb R$ with $1\le K$, if
--
--   $$
--   \forall d\in\mathbb N,\quad 2\le d\ \Longrightarrow\ \operatorname{CumulantBound}\bigl(d,(d!)^2K^d\bigr),
--   $$
--
--   then the following holds for every finite-dimensional complete real inner-product normed space $E$ with measurable Borel structure and second-countable topology, and every probability measure $\mu$ on $E$ that is log-concave and isotropic:
--
--   $$
--   \operatorname{constant}_{\mathrm{Intrinsic}}(\mu)
--   \le \operatorname{ENNReal.ofReal}(2CK).
--   $$
--
--   This declaration extends the regular-potential estimate to arbitrary finite-dimensional isotropic log-concave probability measures and is the main conditional Poincaré assembly.
--
--   **Formalization Note**: The space carries an explicit `FiniteDimensional ℝ E` instance. The Poincaré constant is ENNReal-valued, while the displayed bound is formed with `ENNReal.ofReal`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem localSlope_le_of_cumulantBound_all :
--       ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
--         (∀ d : ℕ, 2 ≤ d → CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
--         ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
--           [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
--           (μ : ProbabilityMeasure E), KLS.LogConcave μ → KLS.Isotropic μ →
--             Poincare.LocalSlope.Intrinsic.constant μ ≤ ENNReal.ofReal (2 * C * K)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Reduction`](https://prove2.me/theorems/777aa78c-b385-4e2a-916c-1b5126410eae).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`exists_ambient_extension`](https://prove2.me/theorems/eca5f601-3244-4c7a-abb0-b647df83122f), [`Isotropic.map_linearIsometryEquiv`](https://prove2.me/theorems/2a04e022-1e2a-44a3-9511-86cbce831c79), [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de), [`localSlope_le_of_regular_isotropic_bound`](https://prove2.me/theorems/621a2407-818c-46e6-9957-c61bcf6e344e).
--
--   Previous: [`poincare_le_of_cumulantBound`](https://prove2.me/theorems/0b4bd144-4221-4e5f-a91d-90cbadac41af) · Next: [`conjecture_of_cumulantBound`](https://prove2.me/theorems/844c5956-2149-46f9-8369-bc8853a7bf38).
--
--   [Source excerpt, lines 307–313](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L307-L313) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 1.1, p. 2. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L302-L330 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Reduction`, declaration `FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
universe u

theorem FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all_readable :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      (∀ d : ℕ, 2 ≤ d → CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
        (μ : ProbabilityMeasure E), KLS.LogConcave μ → KLS.Isotropic μ →
          Poincare.LocalSlope.Intrinsic.constant μ ≤ ENNReal.ofReal (2 * C * K) := by sorry
