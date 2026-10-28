-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_hessian_cutoff_sq_difference_bound_readable
-- name    : FunctionalInequalities.Analysis.exists_hessian_cutoff_sq_difference_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:54.416319+00:00
-- url     : https://prove2.me/theorems/54515687-f5b2-40e0-b262-9c29f518ff9c
-- title:
--   Cutoff Hessian Entry Difference-Quotient Bound
-- statement:
--   This formalizes a supporting component of Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,V,\chi:\mathbb R^n\to\mathbb R$. Assume $u,V\in C^1$ are convex, $\nabla u$ is Lipschitz, $-u+V\circ\nabla u$ is Lipschitz, and for some $K>0$ the almost-everywhere Hessian data satisfy $H_u\succ0$, $\log\det H_u=-u+V(\nabla u)$, and $KI-H_u\succeq0$. Assume also that $u(x+h)+u(x-h)-2u(x)\le D\|h\|^2$ for all $x,h$, and that $\chi\in C_c^1$. For every $i,j$ and $v$, there exists $C\ge0$ such that, whenever $t\ne0$ and $|t|\le1$,
--
--   $$\int\left(\chi(x+tv)H_u(x+tv)_{ij}-\chi(x)H_u(x)_{ij}\right)^2dx\le Ct^2.$$
--
--   This is a global $L^2$ difference-quotient estimate for cutoff Hessian entries.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_hessian_cutoff_sq_difference_bound {n : ℕ}
--       {u V χ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
--       (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
--       {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       {K : ℝ} (hK : 0 < K)
--       (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).PosDef ∧
--         Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
--         (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
--       {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
--       (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
--       (i j : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
--         (∫ x, (χ (x + t • v) * hessianMatrix u (x + t • v) i j -
--           χ x * hessianMatrix u x i j) ^ 2) ≤ C * t ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/HessianIncrement`](https://prove2.me/theorems/ed30c0a7-e1f1-47c8-bf1b-4711117fdb53).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`exists_smooth_compact_translate_majorant`](https://prove2.me/theorems/5a6cfef8-0f99-4ac1-ab61-4c7439b31f8f), [`integrable_hessian_increment_energy`](https://prove2.me/theorems/629a963f-e2b8-40f9-bcc4-6dab330a953b), [`integral_mul_hessian_increment_le`](https://prove2.me/theorems/ed5fdd74-9c13-4186-ad4f-40dd1e40ed9c), [`memLp_cutoff_mul_hessianMatrix_entry`](https://prove2.me/theorems/a87ed401-510c-4f6e-8e89-854801032ee1), [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   Previous: [`integral_mul_hessian_increment_le`](https://prove2.me/theorems/ed5fdd74-9c13-4186-ad4f-40dd1e40ed9c).
--
--   [Source excerpt, lines 267–282](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean#L267-L282) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean#L263-L457 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.HessianIncrement`, declaration `FunctionalInequalities.Analysis.exists_hessian_cutoff_sq_difference_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.exists_hessian_cutoff_sq_difference_bound_readable {n : ℕ}
    {u V χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (i j : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      (∫ x, (χ (x + t • v) * hessianMatrix u (x + t • v) i j -
        χ x * hessianMatrix u x i j) ^ 2) ≤ C * t ^ 2 := by sorry
