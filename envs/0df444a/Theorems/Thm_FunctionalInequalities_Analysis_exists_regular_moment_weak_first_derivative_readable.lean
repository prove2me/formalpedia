-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_first_derivative_readable
-- name    : FunctionalInequalities.Analysis.exists_regular_moment_weak_first_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:16.013169+00:00
-- url     : https://prove2.me/theorems/db7072c4-5f0c-4a46-9f63-f4f194d792ed
-- title:
--   First Weak Monge–Ampère Derivative Package
-- statement:
--   This formalizes the first weak Monge–Ampère derivative identity, corresponding to part of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Under the regular-source hypotheses of the regular moment-potential theorem—$n\ge1$, $\kappa>0$, compact convex $K$ with nonempty interior, smooth $W$, convexity of $W-\frac\kappa2\|\cdot\|^2$, and isotropic $\mu=\mathbf{1}_K e^{-W}dx$—there exist $u,L,L_F,T$ satisfying the convexity, normalization, moment-map, $C^1$, gradient-Lipschitz, exponent-Lipschitz, second-difference, a.e. Hessian, and weak-Hessian-tensor conclusions stated above. In addition, the exponential Monge–Ampère density is Lipschitz and, for every coordinate direction $e_k$, the determinant and logarithmic determinant have weak derivatives
--
--   $$
--   \partial_k\det H_u=\det H_u\,\operatorname{tr}(H_u^{-1}T_k),
--   $$
--
--   and
--
--   $$
--   \partial_k\log\det H_u=\operatorname{tr}(H_u^{-1}T_k).
--   $$
--
--   Almost everywhere these traces equal respectively the derivative of $-u+W(\nabla u)$ and the explicit chain-rule expression
--
--   $$
--   -\partial_k u+\sum_a H_{ka}\,\partial_aW(\nabla u).
--   $$
--
--   All derivative densities are locally in $L^2$ on compact sets.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--           HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
--             (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
--             (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
--           (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--             ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
--               fderiv ℝ (fun y => -u y + W (gradient u y)) x
--                 (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
--           (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--             ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
--               -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
--                 ∑ a : Fin n, hessianMatrix u x k a *
--                   fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/MomentRegularity/WeakDerivative`](https://prove2.me/theorems/7f428f36-c3e2-46b9-8fdd-19a83012aba0).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Selected supporting theorems: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220), [`ae_fderiv_mongeAmpere_exponent`](https://prove2.me/theorems/71049741-6710-4957-9e2a-2a505bfab529), [`exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`](https://prove2.me/theorems/d27371ec-adba-4761-8a3a-e229679243d0), [`exists_regular_moment_weak_tensor`](https://prove2.me/theorems/795e959e-8359-45c4-b731-4112d0057128), [`fderiv_det_eq_det_mul_trace`](https://prove2.me/theorems/7b944e90-ac35-4a2d-a68e-0c989cf61604).
--
--   Previous: [`exists_regular_moment_weak_tensor`](https://prove2.me/theorems/795e959e-8359-45c4-b731-4112d0057128).
--
--   [Source excerpt, lines 158–169](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean#L158-L169) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean#L121-L285 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative`, declaration `FunctionalInequalities.Analysis.exists_regular_moment_weak_first_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakDerivative

open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ Set.univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
include hn hκ hK hKc hKint hW hstrong hμ hiso

theorem FunctionalInequalities.Analysis.exists_regular_moment_weak_first_derivative_readable :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) := by sorry
