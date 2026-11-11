-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_proposition_A_9
-- name    : LowRankMisspec.RankOne.proposition_A_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:04.916745+00:00
-- url     : https://prove2.me/theorems/e8c3da31-ca03-4efa-a8cc-9093664df587
-- title:
--   Proposition A.9 — $\mathcal R_r$ is compact
-- statement:
--   For every integer $r\ge1$, the set of all rank-at-most-$r$ distributions
--   $$\mathcal R_r=\{Q\in\Delta([\sigma]^T):\mathrm{drank}(Q)\le r\}$$
--   is compact (as a subset of $\mathbb R^{[\sigma]^T}$).
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: compact (topology unstated) → IsCompact in (Fin T → Fin σ) → ℝ with the product topology; reason: the Euclidean topology of the finite-dimensional space ℝ^{[σ]^T}
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 17 (PDF 18), Proposition A.9

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Rank

namespace LowRankMisspec.RankOne

/-- Proposition A.9 (`R_r` is compact): for every integer `r ≥ 1`, the set
`R_r = {Q ∈ Δ([σ]^T) : drank(Q) ≤ r}` is a compact subset of `ℝ^{[σ]^T}`. -/
theorem proposition_A_9 {σ T r : ℕ} (hr : 1 ≤ r) : IsCompact (RClass σ T r) := by sorry

end LowRankMisspec.RankOne
