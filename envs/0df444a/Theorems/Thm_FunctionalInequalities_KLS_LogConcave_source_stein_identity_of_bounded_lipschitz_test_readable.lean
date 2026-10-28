-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_source_stein_identity_of_bounded_lipschitz_test_readable
-- name    : FunctionalInequalities.KLS.LogConcave.source_stein_identity_of_bounded_lipschitz_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:47.546714+00:00
-- url     : https://prove2.me/theorems/abe8f632-2fbe-4518-9208-6c81be572011
-- title:
--   Weak Source Stein Identity
-- statement:
--   This statement formalizes the weak source Stein identity associated with a normalized potential.
--
--   Let $n\in\mathbb N$. Let $u,f:\mathbb R^n\to\mathbb R$ be $C^1$, let $u$ and $∇u$ be globally Lipschitz, and assume
--
--   $$
--   \int_{\mathbb R^n}e^{-u(y)}\,dy=1.
--   $$
--
--   Let $f$ be globally Lipschitz and bounded by $C$. For every coordinate $i\in\operatorname{Fin}(n)$, both displayed integrands are integrable with respect to the tilted measure `volume.tilted (-u)`, and
--
--   $$
--   \int (∇u(y))_i f(∇u(y))\,dν(y)
--   =
--   \int \sum_j (\nabla^2u(y))_{ij}(∇f(∇u(y)))_j\,dν(y),
--   $$
--
--   where $ν=\operatorname{volume}.\operatorname{tilted}(-u)$. This is an analytic identity; it does not assert existence of an inverse gradient map or a target Stein kernel.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem source_stein_identity_of_bounded_lipschitz_test {n : ℕ}
--       {u f : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lf : NNReal}
--       (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
--       (hG : LipschitzWith G (gradient u))
--       (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
--       (hf : ContDiff ℝ 1 f) (hfLip : LipschitzWith Lf f)
--       (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) (i : Fin n) :
--       Integrable (fun y => gradient u y i * f (gradient u y))
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
--       Integrable (fun y => ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
--       (∫ y, gradient u y i * f (gradient u y)
--         ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
--         ∫ y, (∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
--           ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HessianStein`](https://prove2.me/theorems/72cb6534-e95d-45a6-ad0a-93acef4b771e).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Supporting theorems: [`integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz`](https://prove2.me/theorems/80255608-689e-4cd7-80cc-3b2a722fd329), [`chain_coordinate_of_differentiableAt_gradient`](https://prove2.me/theorems/5a18cc05-1ac8-4293-a020-60dea2d6f206).
--
--   Next: [`source_affine_stein_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/e5b3ff9c-092e-463b-98ea-ed142c530c1b).
--
--   [Source excerpt, lines 234–248](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HessianStein.lean#L234-L248) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.7 (Fathi [29, Theorem 2.3]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HessianStein.lean#L230-L272 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HessianStein`, declaration `FunctionalInequalities.KLS.LogConcave.source_stein_identity_of_bounded_lipschitz_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein

open MeasureTheory Filter
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 600000

theorem FunctionalInequalities.KLS.LogConcave.source_stein_identity_of_bounded_lipschitz_test_readable {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lf : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hf : ContDiff ℝ 1 f) (hfLip : LipschitzWith Lf f)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) (i : Fin n) :
    Integrable (fun y => gradient u y i * f (gradient u y))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    Integrable (fun y => ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    (∫ y, gradient u y i * f (gradient u y)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ y, (∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by sorry
