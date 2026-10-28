-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_tensor_readable
-- name    : FunctionalInequalities.Analysis.exists_regular_moment_weak_tensor_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:11.583274+00:00
-- url     : https://prove2.me/theorems/795e959e-8359-45c4-b731-4112d0057128
-- title:
--   Regular Moment Potential With Weak Hessian Tensor
-- statement:
--   This formalizes a partial regularity package related to Lemmas 2.2 and Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Assume $n\ge1$, $\kappa>0$, $K$ is compact and convex with nonempty interior, $W$ is smooth, $W-\frac\kappa2\|\cdot\|^2$ is convex, and an isotropic probability measure $\mu$ has density $\mathbf{1}_K e^{-W}$ with respect to Lebesgue measure. Then there exist $u$, $L$, $L_F$, and a tensor $T$ such that:
--
--   1. $u$ is convex, $L$-Lipschitz, $C^1$, normalized by $\int e^{-u}=1$, and its tilted measure maps under $\nabla u$ to $\mu$.
--   2. $\nabla u$ is $(16/\kappa)$-Lipschitz.
--   3. $-u+W\circ\nabla u$ is $L_F$-Lipschitz and
--
--   $$
--    u(x+h)+u(x-h)-2u(x)\le\frac4\kappa\|h\|^2.
--   $$
--
--   4. Almost everywhere, $H_u\succ0$, $\log\det H_u=-u+W(\nabla u)$, and $(16/\kappa)I-H_u\succeq0$.
--   5. $T$ is the weak directional derivative tensor of $H_u$, with every component locally in $L^2$ on compact sets.
--
--   No further classical Hessian regularity is included.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_regular_moment_weak_tensor :
--       ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
--           (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
--         ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
--         (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
--           (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
--         LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
--         (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
--         (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--           (hessianMatrix u x).PosDef ∧
--           Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
--           ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
--         ∀ k i j,
--           HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
--               (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
--             ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--               MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/MomentRegularity/WeakDerivative`](https://prove2.me/theorems/7f428f36-c3e2-46b9-8fdd-19a83012aba0).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`exists_lipschitzWith_neg_add_comp_gradient`](https://prove2.me/theorems/e0b4ed2f-da69-4e68-a1df-7fa0bdfaa735), [`exists_regular_moment_potential`](https://prove2.me/theorems/d91fde05-8ec1-4655-bc90-ed2dd99d4bf3), [`exists_weak_third_derivative`](https://prove2.me/theorems/01da6e3a-40eb-47f5-afa9-095719a6d051), [`secondDifference_le_of_map_gradient`](https://prove2.me/theorems/8a48698f-79ec-4b96-966b-75b5ba3d4373).
--
--   Next: [`exists_regular_moment_weak_first_derivative`](https://prove2.me/theorems/db7072c4-5f0c-4a46-9f63-f4f194d792ed).
--
--   [Source excerpt, lines 48–66](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean#L48-L66) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]); Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean#L45-L86 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative`, declaration `FunctionalInequalities.Analysis.exists_regular_moment_weak_tensor`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.exists_regular_moment_weak_tensor_readable :
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
      ∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
