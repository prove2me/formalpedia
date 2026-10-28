-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integrable_hessian_increment_energy_readable
-- name    : FunctionalInequalities.Analysis.integrable_hessian_increment_energy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:36.799616+00:00
-- url     : https://prove2.me/theorems/629a963f-e2b8-40f9-bcc4-6dab330a953b
-- title:
--   Integrability of Shifted Hessian Increment Energy
-- statement:
--   This is an integrability component related to Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u$ be continuous with Lipschitz gradient, let $\eta$ be continuous and compactly supported, and let $h$ be any vector in $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$. Then the function
--   $$x\mapsto \eta(x)\left(\sum_{i,j}\bigl(H(x+h)_{ij}-H(x)_{ij}\bigr)^2+\sum_{i,j}\bigl(H(x-h)_{ij}-H(x)_{ij}\bigr)^2\right)e^{-u(x)},$$
--   where $H(x)=\operatorname{hessianMatrix}(u,x)$, is integrable with respect to volume.
--
--   This statement provides genuine $L^1$ control for the compactly weighted squared Hessian increments. It does not assert the main integrated Hessian bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_hessian_increment_energy {n : ℕ}
--       {u η : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
--       (hη : Continuous η) (hηc : HasCompactSupport η)
--       (h : EuclideanSpace ℝ (Fin n)) :
--       Integrable (fun x => η x *
--         ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
--          ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) *
--         Real.exp (-u x)) (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/HessianIncrement`](https://prove2.me/theorems/ed30c0a7-e1f1-47c8-bf1b-4711117fdb53).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   Next: [`integral_mul_hessian_increment_le`](https://prove2.me/theorems/ed5fdd74-9c13-4186-ad4f-40dd1e40ed9c).
--
--   [Source excerpt, lines 36–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean#L36-L44) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean#L34-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.HessianIncrement`, declaration `FunctionalInequalities.Analysis.integrable_hessian_increment_energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integrable_hessian_increment_energy_readable {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (h : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => η x *
      ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
       ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) *
      Real.exp (-u x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
