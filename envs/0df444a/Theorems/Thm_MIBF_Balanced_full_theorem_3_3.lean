-- Prove2me | Theorems.Thm_MIBF_Balanced_full_theorem_3_3
-- name    : MIBF.Balanced.full_theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:58:02.756183+00:00
-- url     : https://prove2.me/theorems/9cb374da-e9ab-4b69-b9e4-d0d15ccae9a2
-- title:
--   [Full] Theorem 3.3 — small-boundary Bellman inequality: $\zeta\ge R_\phi$ when $\mu_u\le\mu_w\le10^{-2}$ or $\mu_u+(1-\mu_w)\le10^{-4}$, and their orbits
-- statement:
--   Bits throughout. Let $M=(\mu_u,\mu_w,e_u,e_w)$ be a four-moment tuple with positive entropy coordinates $e_u,e_w>0$ (entropy caps $e_u=H(\mu_u)$ or $e_w=H(\mu_w)$ allowed). Suppose $M$, or one of its images
--   $$E(M)=(\mu_w,\mu_u,e_w,e_u),\quad K(M)=(1-\mu_u,1-\mu_w,e_u,e_w),\quad K(E(M))=(1-\mu_w,1-\mu_u,e_w,e_u)$$
--   under label exchange and simultaneous complement, has its pair of means $(x,y)$ on one of the two branches
--
--   - same-side: $0<x\le y\le 10^{-2}$;
--   - opposite-side: $0<x<\tfrac12<y<1$ and $x+(1-y)\le10^{-4}$.
--
--   Then the balanced Bellman inequality holds at $M$:
--   $$\zeta(M)\ \ge\ R_\phi(M).$$
--   The edge value $\zeta$ is unrestricted: the representing law need not obey any pointwise order.
--
--   This is the part of the balanced Bellman inequality near the corners of the mean square, where the pure-gap argument is not used.
--
--   Differences from the source:
--   - reading: "feasible positive-entropy four-moment tuple" → four-moment tuple (Definition 2.1 box) with $e_u,e_w>0$; reason: feasible tuples are exactly these by [Full] Lemma 2.1.
--   - reading: "Full label exchange and complement give the corresponding upper orientations" → the hypothesis allows $M$, $E(M)$, $K(M)$ or $K(E(M))$ to lie on a branch; reason: this sentence of the statement asserts the inequality on those orientations.
--   - reading: "the zero-entropy limits are included by the endpoint estimates below" → not formalized; reason: the statement is about positive-entropy tuples; the sentence refers to other results ([Full] Theorem 3.13).
--   - encoding: "$T\ge0$" → $R_\phi(M)\le\zeta(M)$ in `EReal`; reason: $T=\zeta-R_\phi$ and $\zeta$ may be $+\infty$.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 13 (PDF 35), Theorem 3.3; symmetries E, K: [Full] p. 28 (PDF 50), (36)–(37)

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue
import Definitions.Def_MIBF_Balanced_BellmanDifference

namespace MIBF.Balanced
theorem full_theorem_3_3 (mu mw eu ew : ℝ) (hM : IsFourMomentTuple mu mw eu ew)
    (heu : 0 < eu) (hew : 0 < ew)
    (hbranch : ∃ x y : ℝ,
      ((x = mu ∧ y = mw) ∨ (x = mw ∧ y = mu) ∨ (x = 1 - mu ∧ y = 1 - mw) ∨
        (x = 1 - mw ∧ y = 1 - mu)) ∧
      ((0 < x ∧ x ≤ y ∧ y ≤ 1 / 100) ∨
        (0 < x ∧ x < 1 / 2 ∧ 1 / 2 < y ∧ y < 1 ∧ x + (1 - y) ≤ 1 / 10000))) :
    ((Rphi mu mw eu ew : ℝ) : EReal) ≤ ((zeta mu mw eu ew : ENNReal) : EReal) := by sorry
end MIBF.Balanced
