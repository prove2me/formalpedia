-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_local_taylor_two_readable
-- name    : FunctionalInequalities.Analysis.local_taylor_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:28.617325+00:00
-- url     : https://prove2.me/theorems/4b2efc81-f85a-4a3c-aec5-38e536f55203
-- title:
--   Local Second-Order Taylor Remainder
-- statement:
--   This is a local Taylor estimate in finite-dimensional Euclidean space.
--
--   Let $\psi:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$ be twice continuously differentiable at $x_0$, and let $\varepsilon>0$. Then there exists $r>0$ such that every $x$ with $\|x-x_0\|<r$ satisfies
--   $$\left|\psi(x)-\left(\psi(x_0)+D\psi(x_0)(x-x_0)+\frac12D^2\psi(x_0)[x-x_0,x-x_0]\right)\right|
--   \le \varepsilon\|x-x_0\|^2.$$
--
--   The result supplies a quantitative second-order remainder bound near one point and is used as a technical ingredient in touching-test arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma local_taylor_two
--       {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
--       {x₀ : EuclideanSpace ℝ (Fin n)}
--       (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
--       ∃ r > 0, ∀ x ∈ ball x₀ r,
--         |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
--           (1 / 2 : ℝ) *
--             (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀))| ≤
--           ε * ‖x - x₀‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Previous: [`hessianMatrix_quadratic`](https://prove2.me/theorems/c1a646b2-00af-48f5-80d5-4c01f3dab8bd) · Next: [`le_det_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/6c79ec26-adc7-48d0-89d1-5a5ef657b31d).
--
--   [Source excerpt, lines 261–269](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L261-L269) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L261-L383 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `_private.FunctionalInequalities.Analysis.Convex.Viscosity.0.FunctionalInequalities.Analysis.local_taylor_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open Set Metric Filter

lemma FunctionalInequalities.Analysis.local_taylor_two_readable
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ ball x₀ r,
      |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
        (1 / 2 : ℝ) *
          (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀))| ≤
        ε * ‖x - x₀‖ ^ 2 := by sorry
