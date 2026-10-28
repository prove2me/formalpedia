-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_regularClass_seq_of_compact_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_regularClass_seq_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:01.907419+00:00
-- url     : https://prove2.me/theorems/87b3bac7-94fd-4a3d-b3c3-f57d65a72c20
-- title:
--   Compact Regular Approximation by Isotropic Uniformly Convex Laws
-- statement:
--   This formalizes the compactly supported part of Lemma A.1 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb N$, let $μ$ be a probability measure on `EuclideanSpace ℝ (Fin n)`, and assume that $μ$ is log-concave, isotropic, and has compact measure support. Then there exists a sequence $(ζ_j)$ of probability measures such that, for every $j$, $ζ_j$ is isotropic and there exist $K_j$, $W_j$, and $κ_j$ with:
--
--   1. $κ_j>0$, $K_j$ compact and convex, and $\operatorname{int}K_j$ nonempty;
--   2. $W_j$ is $C^\infty$ and $y\mapsto W_j(y)-(κ_j/2)\|y\|^2$ is convex on the whole space;
--   3. $ζ_j$ has density `ENNReal.ofReal (exp (-W_j))` restricted to $K_j$ with respect to volume;
--   4. for every $d\le4$ and every $v:\operatorname{Fin}(d)\to\mathbb R^n$, the mixed moments converge:
--
--   $$
--   \int\prod_i\langle v_i,x\rangle\,dζ_j(x)
--   \longrightarrow
--   \int\prod_i\langle v_i,x\rangle\,dμ(x).
--   $$
--
--   The dimension parameter is arbitrary, including $n=0$, exactly as in the Lean statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_regularClass_seq_of_compact {n : ℕ}
--       (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ)
--       (hcompact : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) :
--       ∃ ζ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
--         (∀ j, KLS.Isotropic (ζ j) ∧ ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
--           (κ : ℝ), 0 < κ ∧ IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧ ContDiff ℝ ∞ W ∧
--             ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
--             (ζ j : Measure (EuclideanSpace ℝ (Fin n))) =
--               (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
--                 (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) ∧
--         ∀ d ≤ 4, ∀ v : Fin d → EuclideanSpace ℝ (Fin n),
--           Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ζ j : Measure (EuclideanSpace ℝ (Fin n)))) atTop
--             (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/Letwin/Approximation`](https://prove2.me/theorems/6e41413b-e6b9-4497-be00-27a5ca71753a).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`exists_metric_diagonal`](https://prove2.me/theorems/c1baf226-693c-4f22-b2f1-ccc4640d1cd9), [`row_joint_tendsto`](https://prove2.me/theorems/23822530-689b-4fdf-a9f4-e7013d658d1f), [`smoothedLaw_covarianceBilin`](https://prove2.me/theorems/c357a868-1434-4039-b92d-a0210d64482e), [`smoothedLaw_integral_bounded_tendsto`](https://prove2.me/theorems/0594eb14-470e-44f6-ba57-66325d98a696), [`smoothedLaw_mean`](https://prove2.me/theorems/594d731d-a219-4d57-a38e-26c06cf13154).
--
--   [Source excerpt, lines 91–103](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean#L91-L103) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.1. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean#L87-L245 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.Letwin.Approximation`, declaration `FunctionalInequalities.KLS.LogConcave.exists_regularClass_seq_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_Approximation

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ContDiff

theorem FunctionalInequalities.KLS.LogConcave.exists_regularClass_seq_of_compact_readable {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ)
    (hcompact : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) :
    ∃ ζ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      (∀ j, KLS.Isotropic (ζ j) ∧ ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
        (κ : ℝ), 0 < κ ∧ IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧ ContDiff ℝ ∞ W ∧
          ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
          (ζ j : Measure (EuclideanSpace ℝ (Fin n))) =
            (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) ∧
      ∀ d ≤ 4, ∀ v : Fin d → EuclideanSpace ℝ (Fin n),
        Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ζ j : Measure (EuclideanSpace ℝ (Fin n)))) atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) := by sorry
