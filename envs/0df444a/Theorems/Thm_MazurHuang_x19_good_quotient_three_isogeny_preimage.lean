-- Prove2me | Theorems.Thm_MazurHuang_x19_good_quotient_three_isogeny_preimage
-- name    : MazurHuang.x19_good_quotient_three_isogeny_preimage
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-07T17:45:07.599977+00:00
-- url     : https://prove2.me/theorems/d96b7ce0-6ebb-448d-8ce4-a9ce98cf2798
-- title:
--   Surjectivity of a rational $3$-isogeny onto $t^2=s^3-3(24s+12)^2$ (conductor $19$)
-- statement:
--   Let $E_g: y^2=x^3+(8x+76)^2$ and $E_q: t^2=s^3-3(24s+12)^2$; these are elliptic curves over $\mathbb Q$ of conductor $19$, and $$\phi(x,y)=\left(\frac{9x^3+768x^2+21888x+207936}{x^2},\ \frac{27x^3y-65664xy-1247616y}{x^3}\right)$$ is the Vélu $3$-isogeny $E_g\to E_q$ with kernel the rational flexes $(0,\pm76)$. The theorem states that every affine rational point $(s,t)$ of $E_q$ is $\phi(x,y)$ for some rational point $(x,y)$ of $E_g$ with $x\neq0$, i.e. $\phi:E_g(\mathbb Q)\to E_q(\mathbb Q)$ is surjective.
--
--   This is the complementary (Eisenstein) half of the $3$-isogeny descent that shows the order-three diamond quotient $v^2+v=u^3+u^2+u$ of $X_1(19)$ has only three rational points; it is proved by factoring over $\mathbb Z[\zeta_3]$ and excluding unit classes modulo $27$.
-- source:
--   Xiang Huang, FLT fork, commit 51bbb4f191ad0d3753b87123635c100a638ae580 (Apache-2.0), https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/XDelta19GoodDualDescent.lean (theorem quotient_affine_has_threeIsogeny_preimage), with XDelta19GoodIsogeny.lean (threeIsogenyX, threeIsogenyY) and RationalPointsX135Descent.lean.

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.x19_good_quotient_three_isogeny_preimage (s t : ℚ)
    (h : t ^ 2 = s ^ 3 - 3 * (24 * s + 12) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧ y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2 ∧
      (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3 = t := by sorry
