-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_actual_source_weak_trace_conservativity_data_readable
-- name    : FunctionalInequalities.Analysis.actual_source_weak_trace_conservativity_data_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:53.897109+00:00
-- url     : https://prove2.me/theorems/c4a0bba5-191f-4457-aaab-30694404cab9
-- title:
--   Weak Trace Conservativity Data at a Regular Moment Witness
-- statement:
--   This is a technical existence package for the trace and weak Stein estimates.
--
--   Assume $n>0$, $\kappa>0$, $K\subset\mathbb R^n$ is compact, convex, and has nonempty interior, $W$ is smooth, and $W(y)-\frac\kappa2\|y\|^2$ is convex. Let $\mu$ be the normalized isotropic probability law with density $1_Ke^{-W}$ with respect to Lebesgue measure. Then there exist a potential $u$, constants $L, L_F\in\mathbb{NNReal}$, and a weak third-derivative tensor $T$ such that the full Lean payload holds: $u$ is convex, normalized, $C^1$, globally Lipschitz with Lipschitz gradient, its tilted gradient image is $\mu$, its Hessian is almost-everywhere positive definite and bounded above by $(16/\kappa)I$, and its log-determinant equals $-u+W\circ\nabla u$. The payload also includes weak derivatives and compact-local $L^2$ bounds for the Hessian, determinant, logarithmic determinant, and inverse Hessian; mean-Hessian normalization; weak integration-by-parts identities; cutoff estimates; and, for every positive-semidefinite matrix $B$, integrability and zero-mean conservativity identities for the associated trace expression.
--
--   The conclusion is an existence statement for a single regular witness carrying all these auxiliary identities. It supplies supporting infrastructure rather than a standalone inequality.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--           -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
--         ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
--         let H := fun x => hessianMatrix u x
--         let R := fun x => (H x)⁻¹
--         let Tm := fun x i => Matrix.of fun a b => T x i a b
--         let E := fun x => Matrix.of fun i j => -H x i j +
--           (H x * hessianMatrix W (gradient u x) * H x) i j +
--           (R x * Tm x i * R x * Tm x j).trace
--         let g := fun x => 2 * (B * H x * B * E x).trace +
--           2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
--         Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
--           (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/MomentRegularity/TraceStein`](https://prove2.me/theorems/612796d4-e184-478b-b16b-8d3f0b72bbf4).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Selected supporting theorems: [`hessianMatrixIn_posSemidef`](https://prove2.me/theorems/058f9921-bf17-4a55-978b-a367731b240a), [`ae_weak_third_derivative_symm`](https://prove2.me/theorems/236baf49-0092-428b-8c19-9934eff0cfd3), [`bounded_trace_quadratic_weak_derivative_data`](https://prove2.me/theorems/cc2fdc63-2222-4fdb-85c7-4532eb76bc0c), [`exists_regular_moment_bounded_weak_cutoff_testing`](https://prove2.me/theorems/6a1cac66-e876-4989-9b29-728e3e2018ac), [`integrable_and_integral_eq_zero_of_cutoff_defect`](https://prove2.me/theorems/2557ec3d-6b13-4274-962a-274cb6109e0c).
--
--   Next: [`exists_regular_moment_weak_trace_energy`](https://prove2.me/theorems/8b9295d3-a838-466e-8d9d-2a61f4269613).
--
--   [Source excerpt, lines 831–842](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean#L831-L842) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean#L628-L920 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein`, declaration `_private.FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein.0.FunctionalInequalities.Analysis.actual_source_weak_trace_conservativity_data`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_TraceStein

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
open FunctionalInequalities.Probability.Stein
open MeasureTheory Filter Set Metric Matrix
open scoped ContDiff Topology RealInnerProductSpace
include hn hκ hK hKc hKint hW hstrong hμ hiso
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.actual_source_weak_trace_conservativity_data_readable :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
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
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0 := by sorry
