-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_potential_readable
-- name    : FunctionalInequalities.Analysis.exists_regular_moment_potential_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:02.929255+00:00
-- url     : https://prove2.me/theorems/d91fde05-8ec1-4655-bc90-ed2dd99d4bf3
-- title:
--   Regular Moment Potential
-- statement:
--   This formalizes part of Lemma 2.2 of Letwin (arXiv:2607.24164v1), with the displayed conclusions restricted to the formalized hypotheses.
--
--   Let $n\ge1$, $K\subset\mathbb{R}^n$ be compact, convex, and with nonempty interior, and let $W:\mathbb{R}^n\to\mathbb{R}$ be smooth. Let $\kappa>0$ and assume $y\mapsto W(y)-\frac\kappa2\|y\|^2$ is convex. Let $\mu$ be an isotropic probability measure satisfying
--
--   $$
--   \mu=\mathbf{1}_K e^{-W}\,dx
--   $$
--
--   in the `withDensity` sense. Then there exist $u:\mathbb{R}^n\to\mathbb{R}$ and $L\in[0,\infty)$ such that $u$ is convex, $L$-Lipschitz, normalized by $\int e^{-u}=1$, and its tilted measure pushes forward under $\nabla u$ to $\mu$:
--
--   $$
--   (e^{-u}dx)\circ(\nabla u)^{-1}=\mu.
--   $$
--
--   Moreover, $u\in C^1$, $\nabla u$ is $(16/\kappa)$-Lipschitz, and for almost every $x$ the Hessian $H=\nabla^2u$ is positive definite and satisfies
--
--   $$
--   \log\det H(x)=-u(x)+W(\nabla u(x)),
--   $$
--
--   and
--
--   $$
--   \frac{16}{\kappa}I-H(x)\succeq0.
--   $$
--
--   The space is `EuclideanSpace ℝ (Fin n)` and the almost-everywhere assertions use Lebesgue measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_regular_moment_potential {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
--       {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
--       (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
--       (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
--       (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
--         (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
--           (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
--       (hiso : KLS.Isotropic μ) :
--       ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal), ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
--         (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
--           (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
--         ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--           (hessianMatrix u x).PosDef ∧
--           Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
--           ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/MomentRegularity/Potential`](https://prove2.me/theorems/76e138af-1ba7-464e-acf1-d307e8ead30a).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`contDiff_one_of_map_gradient`](https://prove2.me/theorems/0ffece2e-a383-4c75-b592-04da65ab3fa7), [`eventually_abs_sub_quadratic_le_of_subgradient_expansion`](https://prove2.me/theorems/4ddfd262-d82d-4fdf-95dc-67ccaaffbd1b), [`lipschitzWith_gradient_of_second_difference_le`](https://prove2.me/theorems/b83dfd5c-be3e-4ba7-94af-eada55e6bd84), [`posDef_and_det_eq_of_quadratic_expansion`](https://prove2.me/theorems/fdeb8c35-d7cf-4a28-9642-da29fd09799b), [`secondDifference_le_of_map_gradient`](https://prove2.me/theorems/8a48698f-79ec-4b96-966b-75b5ba3d4373).
--
--   [Source excerpt, lines 32–49](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Potential.lean#L32-L49) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]); Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Potential.lean#L30-L217 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentRegularity.Potential`, declaration `FunctionalInequalities.Analysis.exists_regular_moment_potential`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Potential

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.exists_regular_moment_potential_readable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal), ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by sorry
