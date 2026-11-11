-- Prove2me | Theorems.Thm_HiddenCorr_ERM_lemma_12
-- name    : HiddenCorr.ERM.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:34:30.555478+00:00
-- url     : https://prove2.me/theorems/0a8a9d4c-6a1e-4245-8e5e-fc488be90db6
-- title:
--   Lemma 12 — norm of random vector coefficients: $\|(\sum_i\|\sum_j T_{ij}V_j\|_2^2)^{1/2}\|_{L_p}\le CB\|T\|_F\sqrt p$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $V_1,\dots,V_s\in\mathbb R^k$ be independent centered random vectors with $\|V_j\|_2\le B$ almost surely, and let $T\in\mathbb R^{r\times s}$ be deterministic. For every $p\ge1$,
--   $$\Big\|\Big(\sum_{i=1}^r\Big\|\sum_{j=1}^sT_{ij}V_j\Big\|_2^2\Big)^{1/2}\Big\|_{L_p}\le CB\|T\|_F\sqrt p,$$
--   where $\|T\|_F=(\sum_{i,j}T_{ij}^2)^{1/2}$. Only the vectors $V_j$ need to be independent, not their coordinates.
--
--   It bounds the random coefficient vectors that appear in the off-diagonal part of Theorem 7.
--
--   Differences from the source:
--   - encoding: ‖W‖_{L_p} = (E|W|^p)^{1/p}; ℝ^k → (∫⁻ ENNReal.ofReal W ^ p)^{1/p} with W ≥ 0; EuclideanSpace ℝ (Fin k); the Vⱼ measurable with Bochner mean 0; reason: same quantity; measurability is the paper's footnote 1 and makes 'centered' meaningful
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 61, Lemma 12, Eq. (88) (App. C.3)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Lemma 12** (norm of random vector coefficients), p. 61. There is an absolute constant
`C > 0` such that: let `V₁, …, V_s ∈ ℝ^k` be independent centered random vectors with
`‖Vⱼ‖₂ ≤ B` almost surely, and let `T ∈ ℝ^{r×s}` be deterministic. For every `p ≥ 1`,
`‖(∑_{i=1}^r ‖∑_{j=1}^s T_{ij} Vⱼ‖₂²)^{1/2}‖_{L_p} ≤ C B ‖T‖_F √p` (Eq. (88)). -/
theorem lemma_12 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k s r : ℕ)
        (V : Fin s → Ω → EuclideanSpace ℝ (Fin k)),
        (∀ j, Measurable (V j)) → iIndepFun V P → (∀ j, ∫ ω, V j ω ∂P = 0) →
        ∀ B : ℝ, (∀ j, ∀ᵐ ω ∂P, ‖V j ω‖ ≤ B) →
        ∀ (T : Matrix (Fin r) (Fin s) ℝ) (p : ℝ), 1 ≤ p →
          (∫⁻ ω, ENNReal.ofReal (Real.sqrt (∑ i, ‖∑ j, T i j • V j ω‖ ^ 2)) ^ p ∂P) ^ (1 / p) ≤
            ENNReal.ofReal (C * B * Real.sqrt (∑ i, ∑ j, T i j ^ 2) * Real.sqrt p) := by sorry

end HiddenCorr.ERM
