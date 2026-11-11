-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_proposition_A_7
-- name    : LowRankMisspec.RankOne.proposition_A_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:17:52.400402+00:00
-- url     : https://prove2.me/theorems/94a67b99-13d1-46d3-9841-f93123c74a18
-- title:
--   Proposition A.7 — $\mathrm{drank}(P)=1$ iff $P$ is the product of its marginals
-- statement:
--   A law $P\in\Delta([\sigma]^T)$ has distribution rank $1$ if and only if it is a product distribution, i.e.
--   $$\mathrm{drank}(P)=1\iff P[x]=\prod_{j=1}^T P_j[x_j]\quad\forall x\in[\sigma]^T.$$
--   Hence $\mathcal R_1$ is exactly the set of product laws and $d_1(P)$ is the distance from $P$ to the nearest product law; this is the bridge that lets the learner of Theorem 5.1 compete with $d_1$.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: a distribution P ∈ Δ([σ]^T) → a real function P on Fin T → Fin σ with IsLaw P (nonnegative, summing to 1); reason: the simplex written out; same instances
--   - encoding: "is a product distribution" → IsProductDist P: P x = ∏ j, marginal P j (x j) for every x; reason: the form the proof states it in (p. 15); for a law it is equivalent to P = ⊗_t p_t for some rows p_t
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 15 (PDF 16), Proposition A.7

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Rank

namespace LowRankMisspec.RankOne

/-- Proposition A.7 (equivalence of rank-one and product distributions): a law `P ∈ Δ([σ]^T)` has
`drank(P) = 1` if and only if `P[x] = Π_{j=1}^{T} P_j[x_j]` for every `x ∈ [σ]^T`. -/
theorem proposition_A_7 {σ T : ℕ} (P : Str σ T → ℝ) (hP : IsLaw P) :
    drank P = 1 ↔ IsProductDist P := by sorry

end LowRankMisspec.RankOne
