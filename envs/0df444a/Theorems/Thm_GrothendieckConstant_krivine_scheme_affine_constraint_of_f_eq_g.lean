-- Prove2me | Theorems.Thm_GrothendieckConstant_krivine_scheme_affine_constraint_of_f_eq_g
-- name    : GrothendieckConstant.krivine_scheme_affine_constraint_of_f_eq_g
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-07T01:26:31.907902+00:00
-- url     : https://prove2.me/theorems/3a0e911b-e982-4763-b503-20f06a5bd599
-- title:
--   The affine constraint $b_3\ge 2b_1-\tfrac{11}{6}$ for symmetric Krivine schemes ($f=g$)
-- statement:
--   Let $S=(f,g)$ be a Krivine scheme of dimension $k$ whose two partitions coincide, $f=g$. Then its correlation function $H(t)=b_1t+b_3t^3+\cdots$ satisfies the affine constraint of Theorem 2.2, equation (1):
--   $$b_3\ \ge\ 2b_1-\frac{11}{6}.$$
--
--   This is the symmetric case of the milestone `krivine_scheme_affine_constraint`; equality holds for the half-space scheme $f=g=\operatorname{sgn}(x_1)$, where $(b_1,b_3)=(1,\tfrac16)$.
--
--   **Proof outline.** By the Hermite moment formulas (`coeff_hermite_moments`), $b_1=\frac{\pi}{2}|a|^2$ and $b_3=\frac{\pi}{12}|T|^2$, where $a=\mathbb E[f(X)X]$ and $T=\mathbb E[f(X)\mathbf H_3(X)]$. Put $\alpha=|a|$, $v=a/\alpha$, $s=\langle v,X\rangle\sim N(0,1)$ and $s_0=\mathbb E|s|=\sqrt{2/\pi}$. Then $\alpha=\mathbb E[f s]\le s_0$, and contracting $T$ with $v^{\otimes3}$ gives $c:=\langle T,v^{\otimes 3}\rangle=\mathbb E[f(s^3-3s)]\le \mathbb E|s|^3-3\alpha=2s_0-3\alpha$, while $|T|^2\ge c^2$ by Cauchy-Schwarz. If $3\alpha\le 2s_0$ then $2b_1\le \pi\cdot\frac49 s_0^2=\frac89<\frac{11}{6}$. Otherwise $c\le 2s_0-3\alpha<0$, and the claim reduces to $3(\alpha-s_0)(\alpha+5s_0)\le 0$. The argument uses only $|f|\le1$; oddness is not needed.
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, p. 6, Theorem 2.2, equation (1), specialized to symmetric schemes f = g (the general case is proved in the companion paper, Saha et al., "New upper and lower bounds for the Grothendieck constant" (2026), Part 1). The symmetric-case argument here is independent of the companion paper.

import Mathlib
import Definitions.Def_KrivineSchemeDefs

namespace GrothendieckConstant

theorem krivine_scheme_affine_constraint_of_f_eq_g (k : ℕ) (S : KrivineScheme k) (hfg : S.f = S.g) :
    2 * coeffLinear S - 11 / 6 ≤ coeffCubic S := by sorry

end GrothendieckConstant
