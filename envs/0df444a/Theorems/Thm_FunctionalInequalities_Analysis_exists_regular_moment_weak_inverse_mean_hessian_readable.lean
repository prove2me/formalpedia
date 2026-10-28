-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_inverse_mean_hessian_readable
-- name    : FunctionalInequalities.Analysis.exists_regular_moment_weak_inverse_mean_hessian_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:14.967526+00:00
-- url     : https://prove2.me/theorems/b64484be-d224-455e-abd1-d269ba17fd36
-- title:
--   Weak Inverse-Hessian Package and Mean Hessian
-- statement:
--   This formalizes the weak inverse-Hessian and mean-Hessian portion of the regular moment-map framework, related to Lemma 2.3 of Letwin (arXiv:2607.24164v1).
--
--   Under the regular-source assumptions with $n\ge1$, $\kappa>0$, compact convex $K$ with nonempty interior, smooth $W$, convexity of $W-\frac\kappa2\|\cdot\|^2$, and isotropic density $\mu=\mathbf{1}_K e^{-W}dx$, there exist $u,L,L_F,T$ satisfying the normalized convex moment-map, $C^1$, gradient-Lipschitz, exponent-Lipschitz, second-difference, a.e. Monge–Ampère, and locally $L^2$ weak-Hessian conclusions. They also satisfy the weak determinant and logarithmic determinant identities, the weak inverse-Hessian identity
--
--   $$
--   \partial_k(H_u^{-1})_{ij}=-(H_u^{-1}T_kH_u^{-1})_{ij},
--   $$
--
--   with the associated local $L^2$ and local boundedness statements. Finally, each Hessian entry is integrable under the tilted measure $e^{-u}dx$ and
--
--   $$
--   \int H_u(x)_{ij}\,e^{-u(x)}dx=I_{ij}.
--   $$
--
--   The equality is with respect to the explicitly constructed tilted probability measure.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--             MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
--               (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
--               ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--           ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--             MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
--               ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--         ∀ i j : Fin n,
--           Integrable (fun x => hessianMatrix u x i j)
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
--           (∫ x, hessianMatrix u x i j
--             ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
--             (1 : Matrix (Fin n) (Fin n) ℝ) i j
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/MomentRegularity/WeakHessian`](https://prove2.me/theorems/31ee248b-daaa-4574-a15c-d87e43ddfa6c).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul`](https://prove2.me/theorems/6627935a-8ab5-4069-9ba3-e8134c1348f4), [`exists_regular_moment_weak_first_derivative`](https://prove2.me/theorems/db7072c4-5f0c-4a46-9f63-f4f194d792ed), [`hasWeakDerivAlong_inverse_hessian_of_logdet`](https://prove2.me/theorems/6e913d0c-8e93-456f-8534-533355d49266), [`integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map`](https://prove2.me/theorems/5232fd28-307b-473d-a267-0276d096b8b7), [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   Next: [`exists_regular_moment_weak_hessian_evolution`](https://prove2.me/theorems/619ac8de-0688-40ce-8cae-70f9e5b6bb5e).
--
--   [Source excerpt, lines 185–196](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean#L185-L196) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.3. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean#L136-L262 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian`, declaration `FunctionalInequalities.Analysis.exists_regular_moment_weak_inverse_mean_hessian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakHessian

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

theorem FunctionalInequalities.Analysis.exists_regular_moment_weak_inverse_mean_hessian_readable :
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
      (∀ k : Fin n,
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
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j := by sorry
