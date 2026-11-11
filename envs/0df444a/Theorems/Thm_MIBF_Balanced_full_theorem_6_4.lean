-- Prove2me | Theorems.Thm_MIBF_Balanced_full_theorem_6_4
-- name    : MIBF.Balanced.full_theorem_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:59:28.460078+00:00
-- url     : https://prove2.me/theorems/fe7aa138-2cf8-4c21-969b-74bbabc36f68
-- title:
--   [Full] Theorem 6.4 — pure-gap inequality: $G\ge0$ on the whole retained box $R_S$, $S=10^{-4}$
-- statement:
--   Bits throughout; $S=10^{-4}$. For every $(a,c,e,f)$ with
--   $$0\le a\le c\le\tfrac12,\qquad a+c\ge S,\qquad 0<e\le H(a),\qquad 0<f\le H(c)$$
--   (a point of $R_S$: a canonical feasible tuple with positive entropy coordinates, the seam $a+c=S$ and the entropy caps included), the pure gap at the tuple $(\mu_u,\mu_w,e_u,e_w)=(a,c,e,f)$ is nonnegative:
--   $$G(a,c,e,f)=L_4-R_\phi\ \ge\ 0 .$$
--   By the mean reflection of [Full] Lemma 4.1 and label exchange, every positive-entropy tuple whose lower-half distances satisfy $a+c\ge S$ is carried to such a point, so this is the pure-gap half of the balanced Bellman inequality.
--
--   Differences from the source:
--   - reading: "The analytic reductions, the boundary and stationary-point estimates of Theorem 3.16, and Theorem 3.22 imply that …" → only the mathematical conclusion is stated; reason: those results are proved in the paper, and as hypotheses they would make the statement conditional.
--   - reading: "every canonical feasible tuple with $a+c\ge S$ and positive entropy coordinates" → every point of $R_S$; reason: the canonical chart is $0\le a\le c\le\tfrac12$ ([Full] p. 29) and feasibility is $e\le H(a)$, $f\le H(c)$.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 35 (PDF 57), Theorem 6.4; canonical chart and R_S [Full] p. 29 (PDF 51)

import Mathlib
import Definitions.Def_MIBF_Balanced_PureGap

namespace MIBF.Balanced
theorem full_theorem_6_4 (a c e f : ℝ) (h : InRS a c e f) :
    0 ≤ pureGap a c e f := by sorry
end MIBF.Balanced
