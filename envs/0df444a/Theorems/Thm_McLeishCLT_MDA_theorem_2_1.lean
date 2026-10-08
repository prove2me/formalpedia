-- Prove2me | Theorems.Thm_McLeishCLT_MDA_theorem_2_1
-- name    : McLeishCLT.MDA.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:30:27.58199+00:00
-- url     : https://prove2.me/theorems/d133cb00-c6f1-453f-96ba-6733451cede5
-- title:
--   Theorem (2.1), p. 621 — E T_n → 1, {T_n} UI, Σ_j X²_{n,j} →_p 1, max_j |X_{n,j}| →_p 0 imply S_n →_w N(0, 1)
-- statement:
--   Let $\{X_{n,j};\ 1\le j\le k_n\}$ be an array of real random variables on a probability space $(\Omega,\mathcal F,P)$, $S_n=\sum_jX_{n,j}$, and for real $t$ let $T_n=\prod_{j=1}^{k_n}(1+itX_{n,j})$. Suppose that for every real $t$
--
--   1. $ET_n\to1$,
--   2. $\{T_n\}$ is uniformly integrable,
--   3. $\sum_jX_{n,j}^2\to_p1$, and
--   4. $\max_{j\le k_n}|X_{n,j}|\to_p0$.
--
--   Then
--   $$S_n\xrightarrow{w}N(0,1).$$
--
--   No martingale structure is assumed: this is the abstract reduction from which McLeish derives all his martingale central limit theorems.
--
--   **Formalization Note** The σ-fields of the standing setting play no role in this statement and are omitted. Each $X_{n,j}$ is assumed measurable (a random variable). Convergence in distribution is Mathlib's `TendstoInDistribution` towards the law of the identity under the standard Gaussian measure.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 621, Theorem (2.1)

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Theorem (2.1), p. 621. -/
theorem theorem_2_1 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hXm : ∀ n, ∀ j < k n, Measurable (X n j))
    (ha : ∀ t : ℝ, Tendsto (fun n => ∫ ω, prodT k X t n ω ∂P) atTop (𝓝 1))
    (hb : ∀ t : ℝ, UniformIntegrable (fun n => prodT k X t n) 1 P)
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1))
    (hd : TendstoInMeasure P (fun n => maxAbs k X n) atTop (fun _ => 0)) :
    TendstoInDistribution (fun n => S k X n) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by sorry

end McLeishCLT.MDA
