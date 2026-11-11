-- Prove2me | Theorems.Thm_MIBF_Balanced_full_lemma_2_1
-- name    : MIBF.Balanced.full_lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:58:02.782735+00:00
-- url     : https://prove2.me/theorems/437d1af8-aa18-402d-8fda-103fcbf2e82e
-- title:
--   [Full] Lemma 2.1 — a four-moment tuple is feasible for $\zeta$ iff $0\le\mu_u,\mu_w\le1$, $0\le e_u\le H_2(\mu_u)$, $0\le e_w\le H_2(\mu_w)$
-- statement:
--   Let $H$ be the binary entropy in bits. For real numbers $\mu_u,\mu_w,e_u,e_w$, there exists a joint law of a pair $(U,W)$ of $[0,1]$-valued random variables with
--   $$\mathbb E U=\mu_u,\qquad \mathbb E W=\mu_w,\qquad \mathbb E H(U)=e_u,\qquad \mathbb E H(W)=e_w$$
--   if and only if
--   $$0\le\mu_u,\mu_w\le 1,\qquad 0\le e_u\le H(\mu_u),\qquad 0\le e_w\le H(\mu_w).$$
--   The coupling of $U$ and $W$ is unrestricted. This identifies the domain of the edge value $\zeta$: the four-moment tuples are exactly the tuples for which the infimum defining $\zeta$ is over a nonempty set.
--
--   **Formalization Note** A law is a probability measure on $\mathbb R^2$ giving full mass to $[0,1]^2$ (`fourMomentLaws`); "feasible for $\zeta$" is nonemptiness of that set.
--
--   Differences from the source:
--   - encoding: joint laws of $(U,W)\in[0,1]^2$ → probability measures on $\mathbb R^2$ with $\mu([0,1]^2)=1$; reason: the same laws, Lean's measure-theoretic convention.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 11 (PDF 33), Lemma 2.1

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue

namespace MIBF.Balanced
theorem full_lemma_2_1 (mu mw eu ew : ℝ) :
    (fourMomentLaws mu mw eu ew).Nonempty ↔ IsFourMomentTuple mu mw eu ew := by sorry
end MIBF.Balanced
