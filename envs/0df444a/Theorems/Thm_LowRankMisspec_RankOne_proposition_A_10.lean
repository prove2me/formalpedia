-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_proposition_A_10
-- name    : LowRankMisspec.RankOne.proposition_A_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:06.555388+00:00
-- url     : https://prove2.me/theorems/0035f670-cec0-492f-ad93-1070e1ccfaa6
-- title:
--   Proposition A.10 — a closest distribution of rank at most $r$ exists
-- statement:
--   For every integer $r\ge1$ and every law $P\in\Delta([\sigma]^T)$ there is $Q\in\mathcal R_r$ with
--   $$\|P-Q\|_1=d_r(P).$$
--   So the infimum defining $d_r$ is a minimum; in Theorem 5.1 it supplies the closest product law that Lemma 5.2 is applied to.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: a distribution P ∈ Δ([σ]^T) → a real function P on Fin T → Fin σ with IsLaw P (nonnegative, summing to 1); reason: the simplex written out; same instances
--   - encoding: d_r(P) = min_{Q ∈ R_r} ‖P − Q‖₁ → dR r P = sInf of ‖P − Q‖₁ over Q ∈ R_r; reason: the minimum's existence is exactly this proposition, so it cannot be built into the definition
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 17 (PDF 18), Proposition A.10

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Rank

namespace LowRankMisspec.RankOne

/-- Proposition A.10 (existence of a closest low-rank distribution): for every integer `r ≥ 1` and
every law `P ∈ Δ([σ]^T)` there is `Q ∈ R_r` with `‖P − Q‖₁ = d_r(P)`. -/
theorem proposition_A_10 {σ T r : ℕ} (hr : 1 ≤ r) (P : Str σ T → ℝ) (hP : IsLaw P) :
    ∃ Q ∈ RClass σ T r, l1 P Q = dR r P := by sorry

end LowRankMisspec.RankOne
