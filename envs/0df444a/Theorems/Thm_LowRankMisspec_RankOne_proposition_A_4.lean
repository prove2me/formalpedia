-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_proposition_A_4
-- name    : LowRankMisspec.RankOne.proposition_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:17:43.354872+00:00
-- url     : https://prove2.me/theorems/c3ead34e-33d4-49c8-8330-a6e0dc9f9011
-- title:
--   Proposition A.4 — every law on $[\sigma]^T$ has distribution rank at least 1
-- statement:
--   For every law $P\in\Delta([\sigma]^T)$,
--   $$\mathrm{drank}(P)\ge 1,$$
--   where $\mathrm{drank}(P)=\max_{0\le t\le T}\operatorname{rank}J_t(P)$ (Definition 2.1). With Proposition A.7 it pins $\mathcal R_1$ down as the product laws.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: a distribution P ∈ Δ([σ]^T) → a real function P on Fin T → Fin σ with IsLaw P (nonnegative, summing to 1); reason: the simplex written out; same instances
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 14 (PDF 15), Proposition A.4

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Rank

namespace LowRankMisspec.RankOne

/-- Proposition A.4 (lower bound on distribution rank): every law `P ∈ Δ([σ]^T)` has
`drank(P) ≥ 1`. -/
theorem proposition_A_4 {σ T : ℕ} (P : Str σ T → ℝ) (hP : IsLaw P) : 1 ≤ drank P := by sorry

end LowRankMisspec.RankOne
