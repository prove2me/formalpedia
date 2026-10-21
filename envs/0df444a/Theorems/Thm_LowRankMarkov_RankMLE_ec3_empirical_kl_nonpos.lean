-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_ec3_empirical_kl_nonpos
-- name    : LowRankMarkov.RankMLE.ec3_empirical_kl_nonpos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:14.97361+00:00
-- url     : https://prove2.me/theorems/c5abb7c8-3c25-4617-a142-0b0cbcf0d9f3
-- title:
--   (EC.3), ec2 — D̃_KL(P, P̂^r) = ℓ_n(P̂^r) − ℓ_n(P) ≤ 0, under Remark 2's minoration
-- statement:
--   Let $\alpha,\beta>0$ and let $P$ be a transition matrix of rank $r$ satisfying the $(\alpha/p)$-minoration of Remark 2: $\alpha/p\le P_{jk}\le\beta/p$ for all $j,k$. Then for every trajectory $X_0,\dots,X_n$ and every rank-constrained MLE $\widehat P^r$ of (5),
--   $$\widetilde D_{\mathrm{KL}}(P,\widehat P^r)=\ell_n(\widehat P^r)-\ell_n(P)\le0 .$$
--
--   This is the first step of the proof of Theorem 2: combined with $D_{\mathrm{KL}}=\mathcal L(\widehat P^r)-\mathcal L(P)$ it gives (EC.4), $D_{\mathrm{KL}}(P,\widehat P^r)\le D_{\mathrm{KL}}(P,\widehat P^r)-\widetilde D_{\mathrm{KL}}(P,\widehat P^r)$, which Lemma 3 then controls.
--
--   **Formalization Note** The paper states (EC.3) under Assumption 1, which allows $P_{jk}=0$. Then $P$ is not feasible for (5) (every feasible $Q$ has $Q_{jk}\ge\alpha/p$) and the comparison of $\ell_n(\widehat P^r)$ with $\ell_n(P)$ has no justification. Under minoration and $\operatorname{rank}(P)=r$, $P$ is feasible for (5) and the inequality holds; this is the hypothesis used here and in the goal theorem.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. ec2 (PDF p. 35), (EC.3); minoration from Remark 2, p. 8

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

/-- (EC.3), ec2, arXiv:1907.00113v2, under Remark 2's `(α/p)`-minoration (which makes `P` feasible
for (5)): for every trajectory and every rank-constrained MLE `P̂^r`,
`D̃_KL(P, P̂^r) = ℓ_n(P̂^r) − ℓ_n(P) ≤ 0`. -/
theorem ec3_empirical_kl_nonpos {p r n : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (P : Matrix (Fin p) (Fin p) ℝ) (hP : IsStochastic P) (hrank : P.rank = r)
    (hmin : Minorated α β P) (x : Fin (n + 1) → Fin p) (Q : Matrix (Fin p) (Fin p) ℝ)
    (hQ : IsRankMLE α β r x Q) :
    empKL x P Q ≤ 0 := by sorry

end LowRankMarkov.RankMLE
