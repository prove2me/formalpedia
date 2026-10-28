-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_exists_regularClass_of_cond_closedBall_map_readable
-- name    : FunctionalInequalities.KLS.exists_regularClass_of_cond_closedBall_map_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:07.139663+00:00
-- url     : https://prove2.me/theorems/09f327ff-9750-431b-aefd-04c440b44d3b
-- title:
--   Regular-Class Representation After Ball Conditioning and Affine Transport
-- statement:
--   This statement formalizes Letwin's Lemma A.1 regular-class construction.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $V:E\to\mathbb R$ satisfy `RegularPotential V a b`, let $R>0$, let $L:E\simeq_L E$ be a continuous linear equivalence, and let $c\in E$. Then there exist a set $K\subseteq E$, a function $W:E\to\mathbb R$, and a constant $κ\in\mathbb R$ such that:
--
--   1. $κ>0$, $K$ is compact and convex, and $\operatorname{int}K$ is nonempty;
--   2. $W$ is $C^\infty$ and $y\mapsto W(y)-(κ/2)\|y\|^2$ is convex on all of $E$;
--   3. the affine image of the conditional law of `hV.law` on the closed ball $\overline B(0,R)$ has density
--
--   $$
--   \operatorname{map}\bigl(x\mapsto L(x-c)\bigr)\bigl(\operatorname{cond}(\operatorname{law}(V),\overline B(0,R))\bigr)
--   =
--   \operatorname{volume}.\operatorname{withDensity}\!\left(1_K(y)\,\operatorname{ENNReal.ofReal}(e^{-W(y)})\right).
--   $$
--
--   This is an existence result for compact, smooth, uniformly convex regular approximants.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_regularClass_of_cond_closedBall_map [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {V : E → ℝ} {a b : ℝ} (hV : RegularPotential V a b) {R : ℝ} (hR : 0 < R) (L : E ≃L[ℝ] E)
--       (c : E) :
--       ∃ (K : Set E) (W : E → ℝ) (κ : ℝ), 0 < κ ∧ IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
--         ContDiff ℝ ∞ W ∧ ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
--         (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map (fun x => L (x - c)) =
--           (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/BallConditioning`](https://prove2.me/theorems/2fa3d0ff-8849-4ff0-b13d-3697177849fc).
--
--   Definition modules: [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   Supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`RegularPotential.law_comp_affine`](https://prove2.me/theorems/a3faf409-b5c0-4734-ac62-cbff615f4315).
--
--   Next: [`covariance_tendsto_one`](https://prove2.me/theorems/931a2bcc-f8c0-48ee-8d9a-a38753c18c36).
--
--   [Source excerpt, lines 99–105](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L99-L105) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L95-L183 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.BallConditioning`, declaration `FunctionalInequalities.KLS.exists_regularClass_of_cond_closedBall_map`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.KLS.exists_regularClass_of_cond_closedBall_map_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : E → ℝ} {a b : ℝ} (hV : RegularPotential V a b) {R : ℝ} (hR : 0 < R) (L : E ≃L[ℝ] E)
    (c : E) :
    ∃ (K : Set E) (W : E → ℝ) (κ : ℝ), 0 < κ ∧ IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      ContDiff ℝ ∞ W ∧ ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
      (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map (fun x => L (x - c)) =
        (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by sorry
