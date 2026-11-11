-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_eq_4
-- name    : LowRankMisspec.RankOne.eq_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:16:03.253413+00:00
-- url     : https://prove2.me/theorems/b4f79092-dde7-4370-918e-417f43876e64
-- title:
--   §A.2, Eq. (4) — $\|\otimes_t p_t-\otimes_t r_t\|_1\le\sum_t\|p_t-r_t\|_1$
-- statement:
--   For rows $p_1,\dots,p_T$ and $r_1,\dots,r_T$ in $\Delta([\sigma])$,
--   $$\Big\|\bigotimes_t p_t-\bigotimes_t r_t\Big\|_1\le\sum_t\|p_t-r_t\|_1.$$
--   It is used in the proof of Lemma 5.2 (the repair cost), in the row-estimation step and in the rounding step of Theorem 5.1.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: product distributions ⊗_t p_t, ⊗_t r_t → prodLaw p, prodLaw r with every row a law on Fin σ; reason: the paper's product distributions on [σ]^T
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 17 (PDF 18), §A.2, Eq. (4)

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws

namespace LowRankMisspec.RankOne

/-- §A.2, Eq. (4): for rows `p_t, r_t ∈ Δ([σ])`,
`‖⊗_t p_t − ⊗_t r_t‖₁ ≤ Σ_t ‖p_t − r_t‖₁`. -/
theorem eq_4 {σ T : ℕ} (p r : Fin T → Fin σ → ℝ) (hp : ∀ t, IsLaw (p t)) (hr : ∀ t, IsLaw (r t)) :
    l1 (prodLaw p) (prodLaw r) ≤ ∑ t, l1 (p t) (r t) := by sorry

end LowRankMisspec.RankOne
