-- Prove2me | Theorems.Thm_KTSPBounds_simplex_moment_integral
-- name    : KTSPBounds.simplex_moment_integral
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:12.073097+00:00
-- url     : https://prove2.me/theorems/f828d697-acca-42d9-91af-0f7af2bd465b
-- title:
--   Proof of Lemma 2, p.10 — $\mathcal P_k = 1/(2k)!$
-- statement:
--   For every integer $k$,
--
--   $$
--   \mathcal P_k := \int_{l_1,\dots,l_k \ge 0} \mathbf 1_{l_1+\dots+l_k \le 1} \cdot l_1 \cdots l_k \, dl_1 \cdots dl_k = \frac{1}{(2k)!}.
--   $$
--
--   This Dirichlet-type integral is the source of the factorial in the small-ball bound of Lemma 2.
--
--   Differences from the source:
--   - generalization: k ≥ 1 → every k : ℕ; reason: at k = 0 both sides are 1; the statement for k ≥ 1 is the source claim
--   - encoding: integral of an indicator over the nonnegative orthant → set integral over the simplex {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i ≤ 1}; reason: the same integral
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, proof of Lemma 2, p.10

import Mathlib

namespace KTSPBounds

/-- The integral `𝒫_k = ∫_{l_1,…,l_k ≥ 0} 𝟏_{l_1+⋯+l_k ≤ 1} · l_1 ⋯ l_k dl_1 ⋯ dl_k = 1/(2k)!`
(proof of Lemma 2, p.10), Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1.

**Formalization Note.** Stated for every `k : ℕ`. The paper's range is `k ≥ 1`; at `k = 0` the
space `Fin 0 → ℝ` is one point of mass one and both sides are `1`. -/
theorem simplex_moment_integral (k : ℕ) :
    ∫ l in {l : Fin k → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i ≤ 1}, ∏ i, l i =
      1 / ((2 * k).factorial : ℝ) := by sorry

end KTSPBounds
