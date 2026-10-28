-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_letwinCompactBound_of_regularClass_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_of_regularClass_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:30.094971+00:00
-- url     : https://prove2.me/theorems/a49dd56e-2442-4aae-a07b-6def43badd68
-- title:
--   Reduction of Compact Bounds to the Regular Class
-- statement:
--   This formalizes the reduction in Lemma A.1 and Theorem 1.2 of Letwin (arXiv:2607.24164v1).
--
--   Assume that for every $n>0$, every compact convex $K\subseteq\mathbb R^n$ with nonempty interior, every $C^\infty$ function $W$, every $κ>0$ for which $W-(κ/2)\|\cdot\|^2$ is convex, and every isotropic probability measure $μ$ satisfying
--
--   $$
--   μ=\operatorname{volume}.\operatorname{withDensity}\!\left(1_K(x)\,\operatorname{ENNReal.ofReal}(e^{-W(x)})\right),
--   $$
--
--   the predicate `LetwinQuadraticBound μ` holds. Then `LetwinCompactBound` holds for every compactly supported isotropic log-concave probability measure in every positive dimension.
--
--   This is an implication between bound predicates: it does not itself state a universal KLS estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem letwinCompactBound_of_regularClass
--       (h : ∀ (n : ℕ), 0 < n → ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
--         (κ : ℝ), 0 < κ → IsCompact K → Convex ℝ K → (interior K).Nonempty → ContDiff ℝ ∞ W →
--         ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) →
--         ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
--           (μ : Measure (EuclideanSpace ℝ (Fin n))) =
--             (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
--               (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
--           KLS.Isotropic μ → LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
--       LetwinCompactBound
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/LetwinApproximation`](https://prove2.me/theorems/e9cbfeb1-0297-45a7-8eb7-9cdeed00f517).
--
--   Definition modules: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`letwinQuadraticBound_of_tendsto_moments`](https://prove2.me/theorems/6ecfa844-3974-41e9-92f3-a8a463c1d859), [`exists_integrable_exp_norm`](https://prove2.me/theorems/cae54259-25c9-4b6d-b8ab-140080dd2348), [`exists_regularClass_seq_of_compact`](https://prove2.me/theorems/87b3bac7-94fd-4a3d-b3c3-f57d65a72c20), [`logConcave_of_eq_regularClass`](https://prove2.me/theorems/a4ee60d4-3b28-491b-804e-e9c2455e28ed).
--
--   [Source excerpt, lines 30–39](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean#L30-L39) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 1.2; Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.1. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean#L27-L53 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.LetwinApproximation`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_of_regularClass`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_LetwinApproximation

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Analysis.BakryEmery

theorem FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_of_regularClass_readable
    (h : ∀ (n : ℕ), 0 < n → ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
      (κ : ℝ), 0 < κ → IsCompact K → Convex ℝ K → (interior K).Nonempty → ContDiff ℝ ∞ W →
      ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) →
      ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        (μ : Measure (EuclideanSpace ℝ (Fin n))) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
        KLS.Isotropic μ → LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    LetwinCompactBound := by sorry
