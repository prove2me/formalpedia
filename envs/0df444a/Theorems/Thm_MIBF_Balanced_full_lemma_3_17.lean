-- Prove2me | Theorems.Thm_MIBF_Balanced_full_lemma_3_17
-- name    : MIBF.Balanced.full_lemma_3_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:59:36.813684+00:00
-- url     : https://prove2.me/theorems/871c69f6-3d16-4ce1-a452-8b6629f7f93a
-- title:
--   [Full] Lemma 3.17 — global equal-entropy inequality: $G\ge0$ when $e_u=e_w>0$
-- statement:
--   Bits throughout. Let $M=(\mu_u,\mu_w,e,e)$ be a four-moment tuple with equal positive entropy coordinates $e_u=e_w=e>0$ (so $e\le H(\mu_u)$ and $e\le H(\mu_w)$; the means are otherwise arbitrary and unordered). Then the pure gap is nonnegative:
--   $$G(\mu_u,\mu_w,e,e)=L_4(M)-R_\phi(M)\ \ge\ 0 .$$
--   On the equal-entropy diagonal the closure term vanishes and $G$ reduces to a four-point inequality for the perspective $F$; it is one of the boundary cases of the pure-gap inequality.
--
--   Differences from the source:
--   - reading: "If $e_u=e_w=e>0$" (with $G$ defined on feasible tuples) → hypotheses: $(\mu_u,\mu_w,e,e)$ is a four-moment tuple and $e>0$; reason: $G$ is defined for feasible positive-entropy tuples, which are the four-moment tuples by [Full] Lemma 2.1.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 24 (PDF 46), Lemma 3.17

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue
import Definitions.Def_MIBF_Balanced_PureGap

namespace MIBF.Balanced
theorem full_lemma_3_17 (mu mw e : ℝ) (hM : IsFourMomentTuple mu mw e e) (he : 0 < e) :
    0 ≤ pureGap mu mw e e := by sorry
end MIBF.Balanced
