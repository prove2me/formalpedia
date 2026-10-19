-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_rank_remark_nuclear_le
-- name    : LowRankMarkov.RankMLE.rank_remark_nuclear_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:56.990628+00:00
-- url     : https://prove2.me/theorems/85f2bc8d-d7fb-440f-86c4-8d0ab230dcfb
-- title:
--   Rank remark, p. 14 — rank(Q) ≤ r = rank(P) gives rank(Q − P) ≤ 2r and ‖Q − P‖_* ≤ (2r)^{1/2}‖Q − P‖_F
-- statement:
--   Let $P,Q\in\mathbb R^{p\times p}$ with $\operatorname{rank}(P)=r$ and $\operatorname{rank}(Q)\le r$, and put $\Delta=Q-P$. Then
--   $$\operatorname{rank}(\Delta)\le 2r\qquad\text{and}\qquad \|\Delta\|_*\le(2r)^{1/2}\,\|\Delta\|_F ,$$
--   where $\|\cdot\|_*$ is the nuclear norm (sum of singular values) and $\|\cdot\|_F$ the Frobenius norm.
--
--   Applied to $Q=\widehat P^r$, any matrix feasible for the rank-constrained problem (5), this is the paper's remark that the error $\widehat{\boldsymbol\Delta}(r)=\widehat P^r-P$ lies in a nuclear-norm cone, so that the uniform concentration of Lemma 3 applies to the rank-constrained estimator.
--
--   **Formalization Note** The norms are `nuclearNorm` and `frobNorm` of the published definition `CaiCandesShen.Convergence.Basic`. The statement is made for every $Q$ of rank at most $r$, which is what the remark uses about $\widehat P^r$.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. 14, last paragraph of §3.3 (after Lemma 3)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace LowRankMarkov.RankMLE

open CaiCandesShen.Convergence

/-- The rank remark of p. 14 (last paragraph of §3.3), arXiv:1907.00113v2: if `rank(P) = r` and
`rank(Q) ≤ r` (the rank constraint of (5)), then `Δ = Q − P` has `rank(Δ) ≤ 2r` and
`‖Δ‖_* ≤ (2r)^{1/2} ‖Δ‖_F`. -/
theorem rank_remark_nuclear_le {p r : ℕ} (P Q : Matrix (Fin p) (Fin p) ℝ)
    (hP : P.rank = r) (hQ : Q.rank ≤ r) :
    (Q - P).rank ≤ 2 * r ∧
      nuclearNorm (Q - P) ≤ Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) := by sorry

end LowRankMarkov.RankMLE
