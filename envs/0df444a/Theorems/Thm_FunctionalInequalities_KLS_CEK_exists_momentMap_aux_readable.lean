-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_momentMap_aux_readable
-- name    : FunctionalInequalities.KLS.CEK.exists_momentMap_aux_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:27.852809+00:00
-- url     : https://prove2.me/theorems/1fd289ed-c284-4ad8-8eb2-70df86b06ac1
-- title:
--   Weak Moment Map for a Bounded Isotropic Law
-- statement:
--   This is the auxiliary form of the weak moment-map existence statement.
--
--   Let $E$ be finite-dimensional with Borel structure, let $\mu$ be an isotropic probability measure, and let $L\in[0,\infty)$. Assume $\|y\|\le L$ for $\mu$-almost every $y$. Then there exists $\psi:E\to\mathbb{R}$ such that $\psi$ is convex, $L$-Lipschitz, and normalized by
--
--   $$
--   \int e^{-\psi(x)}\,dx=1.
--   $$
--
--   Furthermore, the tilted Lebesgue measure pushes forward under the gradient to $\mu$:
--
--   $$
--   \bigl(dx\bigr)_{e^{-\psi}}\!\mathop{\longmapsto}^{\nabla\psi}\mu.
--   $$
--
--   Equivalently, `((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ`. The statement claims no additional regularity of $\psi$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem exists_momentMap_aux (μ : ProbabilityMeasure E)
--       (hμ : KLS.Isotropic μ) (L : NNReal) (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
--       ∃ ψ : E → ℝ, ConvexOn ℝ (univ : Set E) ψ ∧ LipschitzWith L ψ ∧
--         (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
--         ((volume : Measure E).tilted (fun x => -ψ x)).map (gradient ψ) = (μ : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/MomentMap`](https://prove2.me/theorems/a13c53cf-ecfe-4a6a-bd4e-0464d3687bba).
--
--   Definition modules: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Supporting theorems: [`legendre_bounded_perturbation_finite_curve`](https://prove2.me/theorems/f81ed50e-1e1f-44d9-a9cd-afd086601533), [`bounded_source_lipschitz_primal`](https://prove2.me/theorems/4d577172-78b7-4778-9049-c25519fd30dc), [`hasDerivAt_integral_exp_neg_legendre_add_smul`](https://prove2.me/theorems/302acb49-a8f6-47fd-812e-b58a38e4f610).
--
--   [Source excerpt, lines 32–36](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentMap.lean#L32-L36) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentMap.lean#L26-L341 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentMap`, declaration `_private.FunctionalInequalities.KLS.CEK.MomentMap.0.FunctionalInequalities.KLS.CEK.exists_momentMap_aux`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentMap

open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.exists_momentMap_aux_readable (μ : ProbabilityMeasure E)
    (hμ : KLS.Isotropic μ) (L : NNReal) (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ ψ : E → ℝ, ConvexOn ℝ (univ : Set E) ψ ∧ LipschitzWith L ψ ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (fun x => -ψ x)).map (gradient ψ) = (μ : Measure E) := by sorry
