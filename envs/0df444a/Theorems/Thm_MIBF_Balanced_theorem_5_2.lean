-- Prove2me | Theorems.Thm_MIBF_Balanced_theorem_5_2
-- name    : MIBF.Balanced.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:58:02.753691+00:00
-- url     : https://prove2.me/theorems/1cfcfd61-d2bb-42a7-b3fc-3da9a46bcd2a
-- title:
--   Theorem 5.2 (= [Full] Theorem 7.1) — balanced Bellman inequality: $\zeta(M)\ge R_\phi(M)$ for every $M\in\mathcal M_+$
-- statement:
--   Bits throughout. Let $H$ be the binary entropy, $j$ the Jeffreys edge cost with its lower-semicontinuous boundary extension ($j(0,0)=j(1,1)=0$, $j=+\infty$ at the other boundary points of $[0,1]^2$), and $\phi(m,e)=\eta(e)-F(|1-2m|,e)$ the balanced candidate. For every tuple $M=(\mu_u,\mu_w,e_u,e_w)$ with
--   $$0<\mu_u,\mu_w<1,\qquad 0<e_u\le H(\mu_u),\qquad 0<e_w\le H(\mu_w)$$
--   (the set $\mathcal M_+$; entropy caps included, no ordering of the means),
--   $$\zeta(M)=\inf\Bigl\{\mathbb E\,j(U,W):\ U,W\in[0,1],\ \mathbb EU=\mu_u,\ \mathbb EW=\mu_w,\ \mathbb EH(U)=e_u,\ \mathbb EH(W)=e_w\Bigr\}\ \ge\ R_\phi(M),$$
--   where the infimum is over **all** joint laws of $(U,W)$ on $[0,1]^2$ and
--   $$R_\phi(M)=\phi\Bigl(\frac{\mu_u+\mu_w}{2},\frac{e_u+e_w}{2}\Bigr)-\tfrac12\phi(\mu_u,e_u)-\tfrac12\phi(\mu_w,e_w).$$
--
--   This is the balanced Bellman inequality posed as Conjecture 3 of Chen–Gohari–Nair (2025). By static induction over the Boolean cube it bounds the edge energy of any $(0,1)$-valued array by $\phi$ of its mean and mean entropy, which yields the Courtade–Kumar inequality for balanced Boolean functions.
--
--   **Formalization Note** $\zeta$ is the infimum in $[0,+\infty]$ of lower Lebesgue integrals of the extended cost over probability measures on $\mathbb R^2$ with full mass on $[0,1]^2$ (`zeta`), and the inequality is between extended reals.
--
--   Differences from the source:
--   - encoding: nats ($h$, $\ln 2$ as entropy maximum) → bits ($H$, maximum $1$), on the published `GeneralCK` functions; reason: $\zeta$ and every term of $R_\phi$ scale by $1/\ln 2$, so the inequality has the same instances; in bits it reads exactly as [Full] Theorem 7.1.
--   - encoding: $\zeta(M)\in[0,+\infty]$, an infimum over joint laws on $[0,1]^2$ → infimum in `ℝ≥0∞` over probability measures on $\mathbb R^2$ with $\mu([0,1]^2)=1$, compared with $R_\phi(M)$ in `EReal`; reason: the same laws; the infimum of the empty set is $+\infty$.
--   - reading: [Full] Theorem 7.1's preamble "The analytic reductions, … and Theorem 3.22 imply that" → not a hypothesis; reason: the front statement (Theorem 5.2) is unconditional, and those results are proved in the paper.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 15, Theorem 5.2 (M+ defined p. 8); = [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 36 (PDF 58), Theorem 7.1

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue
import Definitions.Def_MIBF_Balanced_BellmanDifference

namespace MIBF.Balanced
theorem theorem_5_2 (mu mw eu ew : ℝ) (hmu : 0 < mu ∧ mu < 1) (hmw : 0 < mw ∧ mw < 1)
    (heu : 0 < eu ∧ eu ≤ GeneralCK.H mu) (hew : 0 < ew ∧ ew ≤ GeneralCK.H mw) :
    ((Rphi mu mw eu ew : ℝ) : EReal) ≤ ((zeta mu mw eu ew : ENNReal) : EReal) := by sorry
end MIBF.Balanced
