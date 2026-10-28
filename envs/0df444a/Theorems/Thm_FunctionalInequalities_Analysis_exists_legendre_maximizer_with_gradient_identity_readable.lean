-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_legendre_maximizer_with_gradient_identity_readable
-- name    : FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:21.817258+00:00
-- url     : https://prove2.me/theorems/0a4c46db-2543-480e-9c88-e7e91f832b89
-- title:
--   Legendre Maximizer and Dual Gradient
-- statement:
--   This is an attainment statement for the Legendre transform.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential` and lower semicontinuous, and let $y$ belong to the interior of $\{q:\phi^*(q)\ne+\infty\}$. Then there exists $z\in E$ such that
--
--   $$\langle z,y\rangle-\phi(z)=\phi^*(y).$$
--
--   Moreover, if $q\mapsto(\phi^*(q))_{\mathrm{toReal}}$ is differentiable at $y$, then
--   $$z=\nabla\big((\phi^*)_{\mathrm{toReal}}\big)(y).$$
--
--   Thus every interior point of the finite Legendre domain has a primal maximizer, with the stated gradient identification under the additional differentiability implication.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_legendre_maximizer_with_gradient_identity
--       (φ : E → EReal) (hφ : ProperPotential φ)
--       (hlsc : LowerSemicontinuous φ) (y : E)
--       (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
--       ∃ z : E,
--         (inner ℝ z y : EReal) - φ z = legendre φ y ∧
--         (DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y →
--           z = gradient (fun q : E => (legendre φ q).toReal) y)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Attainment`](https://prove2.me/theorems/8fff00c5-0262-4f99-9cab-27221baba48b).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`conjugate_maximizer_eq_gradient`](https://prove2.me/theorems/80335e95-bd3b-41ae-b542-89eb54c17879), [`exists_finite_maximum_of_upperSemicontinuous_linear_decay`](https://prove2.me/theorems/3017df1c-42c0-4624-946f-b456d3bec309), [`tiltedObjective_data`](https://prove2.me/theorems/e3e2f5b2-8368-425f-a963-03a46f5caf8c).
--
--   Previous: [`tiltedObjective_data`](https://prove2.me/theorems/e3e2f5b2-8368-425f-a963-03a46f5caf8c).
--
--   [Source excerpt, lines 337–344](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L337-L344) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L334-L370 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity_readable
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    ∃ z : E,
      (inner ℝ z y : EReal) - φ z = legendre φ y ∧
      (DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y →
        z = gradient (fun q : E => (legendre φ q).toReal) y) := by sorry
