-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_hessian_evolution_readable
-- name    : FunctionalInequalities.Analysis.exists_regular_moment_weak_hessian_evolution_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:58.118241+00:00
-- url     : https://prove2.me/theorems/619ac8de-0688-40ce-8cae-70f9e5b6bb5e
-- title:
--   Regular Moment Witness with Weak Hessian Evolution
-- statement:
--   This formalizes part of Lemma 2.4 of Letwin (arXiv:2607.24164v1), by extending the regular moment witness with weak Hessian evolution data.
--
--   Assume $n>0$, $\kappa>0$, $K$ is compact, convex, and has nonempty interior, $W$ is smooth, and $W(y)-\frac\kappa2\|y\|^2$ is convex on all of $\mathbb R^n$. Let $\mu$ be a probability measure whose density is $e^{-W}$ on $K$ and zero outside $K$, and assume that $\mu$ is isotropic.
--
--   Then there exist $u:\mathbb R^n\to\mathbb R$, $L,LF\in[0,\infty)$, and a tensor $T_{kij}$ such that the previously established regular moment properties hold: $u$ is convex and Lipschitz, $\int e^{-u}=1$, the tilted measure $e^{-u}dx$ pushed forward by $\nabla u$ equals $\mu$, $u$ is $C^1$, $\nabla u$ is Lipschitz with constant $\operatorname{toNNReal}(16/\kappa)$, and $-u+W\circ\nabla u$ is Lipschitz. Moreover,
--
--   $$
--   u:=e^{-u}dx
--   $$
--   is the normalized tilted measure, and
--
--   $$
--    u(x+h)+u(x-h)-2u(x)\le \frac4\kappa\|h\|^2.
--   $$
--
--   Almost everywhere, $\nabla^2u$ is positive definite,
--   $$
--   \log\det\nabla^2u=-u+W(\nabla u),
--   \qquad
--   \frac{16}{\kappa}I-\nabla^2u\succeq0.
--   $$
--
--   The tensor $T$ is a compact-local $L^2$ weak derivative of the Hessian. The declaration also supplies a Lipschitz representative for $e^{-u+W(\nabla u)}$, weak derivatives and compact-local bounds for the determinant and log determinant, the inverse-Hessian weak derivative formula with local $L^2$ and `ENNReal` local $L^\infty$ bounds, integrability and mean identity
--   $$
--   \int (\nabla^2u)_{ij}\,d\nu=\delta_{ij},
--   $$
--   the weak derivative of the first Monge–Ampère trace, the unweighted flux identity, and the weighted curvature–Gram identity stated above.
--
--   This existential declaration packages the complete regular witness needed by later weak evolution and testing results. It asserts existence of these data, not a universal estimate.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--         LocallyIntegrable (fun x => E x i j)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
--           ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--           (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
--             fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
--             ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--           -(∫ x, Real.exp (-u x) * E x i j * ψ x
--             ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/MomentRegularity/WeakHessian`](https://prove2.me/theorems/31ee248b-daaa-4574-a15c-d87e43ddfa6c).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220), [`exists_regular_moment_weak_inverse_mean_hessian`](https://prove2.me/theorems/b64484be-d224-455e-abd1-d269ba17fd36), [`hasWeakDerivAlong_mongeAmpere_first_rhs`](https://prove2.me/theorems/55f12f10-6c36-4776-96b3-387313b3b590), [`integral_exp_neg_hessian_flux_eq_curvature_gram`](https://prove2.me/theorems/6d3ddc0c-45c1-4c79-b3d0-33799314293f), [`integral_weak_hessian_flux_eq_trace_derivative`](https://prove2.me/theorems/6d0b46f6-29ee-4cf1-8e3f-098cb8c41989).
--
--   Previous: [`exists_regular_moment_weak_inverse_mean_hessian`](https://prove2.me/theorems/b64484be-d224-455e-abd1-d269ba17fd36) · Next: [`exists_regular_moment_bounded_weak_hessian_testing`](https://prove2.me/theorems/dc4e4140-f06c-4b2c-a4ae-c740aa939d81).
--
--   [Source excerpt, lines 455–466](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean#L455-L466) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean#L338-L502 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian`, declaration `FunctionalInequalities.Analysis.exists_regular_moment_weak_hessian_evolution`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.exists_regular_moment_weak_hessian_evolution_readable :
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
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by sorry
