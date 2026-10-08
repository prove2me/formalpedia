-- Prove2me | Theorems.Thm_McLeishCLT_MDA_eq_2_5
-- name    : McLeishCLT.MDA.eq_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:33:28.604742+00:00
-- url     : https://prove2.me/theorems/855a3631-9829-45fb-9d50-0965ebacc9c1
-- title:
--   (2.5), p. 622 — P(Z_{n,j} ≠ X_{n,j} for some j ≤ k_n) ≤ P(Σ_j X²_{n,j} > 2) → 0
-- statement:
--   Let $\{X_{n,j};\ 1\le j\le k_n\}$ be an array of real random variables with $\sum_jX_{n,j}^2\to_p1$, and let $Z_{n,j}=X_{n,j}\,I(\sum_{k=1}^{j-1}X_{n,k}^2\le2)$. Then for every $n$
--   $$P\big(Z_{n,j}\ne X_{n,j}\text{ for some }j\le k_n\big)\le P\Big(\sum_jX_{n,j}^2>2\Big),$$
--   and the right-hand side tends to $0$ as $n\to\infty$.
--
--   Display (2.5) shows that the truncated array is asymptotically equivalent to the original one, so it suffices to prove the central limit theorem for $\sum_jZ_{n,j}$.
--
--   **Formalization Note** Only condition (2.3 c) is assumed; the martingale property is not needed for (2.5).
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 622, display (2.5) in the proof of Theorem (2.3)

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- (2.5), p. 622: `P(Z_{n,j} ≠ X_{n,j} for some j ≤ k_n) ≤ P(Σ_j X²_{n,j} > 2) → 0`. -/
theorem eq_2_5 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1)) :
    (∀ n, P {ω | ∃ j < k n, trunc X n j ω ≠ X n j ω} ≤ P {ω | 2 < sumSq k X n ω}) ∧
      Tendsto (fun n => P {ω | 2 < sumSq k X n ω}) atTop (𝓝 0) := by sorry

end McLeishCLT.MDA
