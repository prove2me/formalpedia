-- Prove2me | Theorems.Thm_KTSPBounds_mallows_multinomial
-- name    : KTSPBounds.mallows_multinomial
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:50.733863+00:00
-- url     : https://prove2.me/theorems/ee25d3be-315f-4414-865f-0fd568e43f72
-- title:
--   Bonferroni–Mallows bound for multinomials, p.12
-- statement:
--   Let $(X_1,\dots,X_P)$ be the cell counts of $n$ independent draws from a probability law on $P$ cells, and let $c_1,\dots,c_P$ be nonnegative integers. Then
--
--   $$
--   \mathbb P[X_1 \le c_1, \dots, X_P \le c_P] \le \prod_{i=1}^P \mathbb P(X_i \le c_i).
--   $$
--
--   The upper bound of Theorem 2 uses this to control the probability that no cell receives $k$ points.
--
--   Differences from the source:
--   - generalization: uniform cell probabilities 1/P_α and thresholds k − 1 → any probability law μ on Fin P and any thresholds c : Fin P → ℕ; reason: the form of Mallows 1968; it specializes to the source case, and the corrected upper bound needs non-uniform cells
--   - encoding: ℙ[⋃ A_i^α] = 1 − ℙ[X_1^α ≤ k − 1, ⋯] ≥ 1 − ∏ ℙ(X_i^α ≤ k − 1) → ℙ[∀ i, X_i ≤ c_i] ≤ ∏ ℙ(X_i ≤ c_i); reason: the complement of the same event; the first equality of the display is De Morgan
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, §3.2, p.12 (Bonferroni–Mallows bound, cited from Mallows 1968)

import Mathlib
import Definitions.Def_KTSPBounds_cellCount

open MeasureTheory

namespace KTSPBounds

/-- The Bonferroni–Mallows bound for multinomials (p.12, cited there from Mallows 1968),
Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: if `X_1, …, X_P` are the cell counts of `n` independent draws from a
probability law on `P` cells, then `ℙ[X_1 ≤ c_1, …, X_P ≤ c_P] ≤ ∏_i ℙ(X_i ≤ c_i)`.

**Formalization Note.** The paper uses uniform cells and `c_i = k - 1`. The statement here allows
any law `μ` on the cells and any thresholds, which is the form of Mallows's inequality. The draws
have joint law `Measure.pi` on `Fin n → Fin P`; `Fin P` carries its discrete σ-algebra. -/
theorem mallows_multinomial (n P : ℕ) (μ : Measure (Fin P)) [IsProbabilityMeasure μ]
    (c : Fin P → ℕ) :
    (Measure.pi fun _ : Fin n => μ) {y | ∀ i, cellCount y i ≤ c i} ≤
      ∏ i, (Measure.pi fun _ : Fin n => μ) {y | cellCount y i ≤ c i} := by sorry

end KTSPBounds
