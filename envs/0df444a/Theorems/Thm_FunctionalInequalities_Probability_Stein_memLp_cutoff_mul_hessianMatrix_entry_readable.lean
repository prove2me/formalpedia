-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Stein_memLp_cutoff_mul_hessianMatrix_entry_readable
-- name    : FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:31.446094+00:00
-- url     : https://prove2.me/theorems/a87ed401-510c-4f6e-8e89-854801032ee1
-- title:
--   Compactly Cutoff Hessian Entries Are Global $L^2$
-- statement:
--   This formalizes a technical weak-Hessian integrability statement associated with Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,\chi:\mathbb R^n\to\mathbb R$, assume that $\nabla u$ is globally Lipschitz, and let $i,j\in\mathrm{Fin}\ n$. If $\chi$ is continuous and compactly supported, then the function $x\mapsto\chi(x)\,\operatorname{hessianMatrix}(u)(x)_{ij}$ belongs to $L^2$ with respect to Lebesgue volume:
--
--   $$\chi(x)\,\operatorname{hessianMatrix}(u)(x)_{ij}\in L^2(\mathbb R^n,dx).$$
--
--   This provides a global $L^2$ cutoff interface for a Hessian entry that is controlled locally by the Lipschitz gradient assumption.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Stein`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem memLp_cutoff_mul_hessianMatrix_entry {n : ℕ}
--       {u χ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
--       (hG : LipschitzWith G (gradient u)) (i j : Fin n)
--       (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
--       MemLp (fun x => χ x * hessianMatrix u x i j) 2
--         (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Supporting theorems: [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   Previous: [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6) · Next: [`chain_coordinate_of_differentiableAt_gradient`](https://prove2.me/theorems/5a18cc05-1ac8-4293-a020-60dea2d6f206).
--
--   [Source excerpt, lines 451–456](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L451-L456) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L449-L490 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, declaration `FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian

open MeasureTheory Set

theorem FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry_readable {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x * hessianMatrix u x i j) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
