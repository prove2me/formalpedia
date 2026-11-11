-- Prove2me | Theorems.Thm_MIBF_Balanced_theorem_4_2
-- name    : MIBF.Balanced.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:59:03.131465+00:00
-- url     : https://prove2.me/theorems/5f411d76-8f8e-4f9c-a4bd-fadd2c0b617e
-- title:
--   Theorem 4.2 (= [Full] Theorem 3.1) — global four-moment bound $\zeta(M)\ge L_1(M)$ at every four-moment tuple
-- statement:
--   Bits throughout. For every four-moment tuple $M=(\mu_u,\mu_w,e_u,e_w)$ (that is, $0\le\mu_u,\mu_w\le1$, $0\le e_u\le H(\mu_u)$, $0\le e_w\le H(\mu_w)$, zero entropies included), with the boundary conventions of the extended Jeffreys cost,
--   $$\zeta(M)\ \ge\ L_1(M)=F\Bigl(|\mu_w-\mu_u|,\ \frac{e_u+e_w}{2}\Bigr)+\bar\kappa(e_u,e_w),$$
--   where $\zeta$ is the unrestricted edge value, $F$ is the perspective with $F(0,e)=0$ and $F(s,0)=+\infty$ for $s\ne0$, and $\bar\kappa$ is the lower-semicontinuous closure of $\tilde\kappa(e_1,e_2)=\kappa(\iota(e_1),\iota(e_2))$. The inequality is between extended reals.
--
--   The right side depends only on the four moments, so this reduces the infinite-dimensional infimum over couplings to an explicit function; the pure gap $G=L_1-R_\phi$ is then the quantity whose sign is studied.
--
--   Differences from the source:
--   - encoding: nats → bits; reason: every term scales by $1/\ln 2$; in bits this is [Full] Theorem 3.1 exactly ($L_1=L_4$).
--   - encoding: $\zeta\in[0,+\infty]$ and $L_1\in(-\infty,+\infty]$ → `zeta` in $[0,+\infty]$ and `L4` in `EReal`, compared in `EReal`; reason: Lean convention; same instances.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 11, Theorem 4.2, eq. (20); = [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 12 (PDF 34), Theorem 3.1, eq. (16)

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue
import Definitions.Def_MIBF_Balanced_PureGap

namespace MIBF.Balanced
theorem theorem_4_2 (mu mw eu ew : ℝ) (hM : IsFourMomentTuple mu mw eu ew) :
    L4 mu mw eu ew ≤ ((zeta mu mw eu ew : ENNReal) : EReal) := by sorry
end MIBF.Balanced
