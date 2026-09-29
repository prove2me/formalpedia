-- Prove2me | Theorems.Thm_ModularCurve_fifteenIsogenyJ_of_hauptmodul_memberships
-- name    : ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/cd59e12f-2fae-51e5-9700-596d0507fcbd
-- title:
--   Two hauptmodul relations pin C/D to four values
-- statement:
--   The assertion is an elementary statement about four rational numbers. Let $D, C, u, v \in \mathbb{Q}$ with $D \neq 0$, and suppose the two polynomial relations
--   $$(u+27)(u+3)^3\,D = C\,u, \qquad (v^2+10v+5)^3\,D = C\,v$$
--   hold; that is, $C/D$ is simultaneously the value at $u$ of the classical level-$3$ hauptmodul parametrisation $j = (u+27)(u+3)^3/u$ of the $j$-line and the value at $v$ of the level-$5$ parametrisation $j = (v^2+10v+5)^3/v$, the relations being written multiplicatively so that no division occurs and no a priori hypothesis $u \neq 0$ or $v \neq 0$ is needed. The conclusion is the disjunction of four equalities: $C = -\tfrac{25}{2}D$, or $C = -\tfrac{349938025}{8}D$, or $C = -\tfrac{121945}{32}D$, or $C = \tfrac{46969655}{32768}D$. Thus the ratio $C/D$ is one of the four rational numbers $-25/2$, $-349938025/8$, $-121945/32$, $46969655/32768$. Nothing about elliptic curves or modular curves enters the statement; $D$ and $C$ are free rational parameters, and the conclusion is stated as a multiplicative identity between $C$ and $D$ rather than as a statement about a quotient.
--
--   Classically this is the determination of the non-cuspidal rational points of $X_0(15)$, viewed as the fibre product over the $j$-line of the level-$3$ and level-$5$ hauptmodul parametrisations: an elliptic curve over $\mathbb{Q}$ admitting rational cyclic $3$- and $5$-isogenies has $j$-invariant one of four values, those of the curves in the isogeny class of conductor $50$. The formal statement is the purely rational-arithmetic shadow of this: the quantities $D$ and $C$ are unconstrained rationals playing the roles of $\Delta$ and $c_4^3$, and the four conclusions are the corresponding values of $c_4^3/\Delta$. It is used to prove [`WeierstrassCurve.fifteenIsogenyClassification`](thm.html#WeierstrassCurve.fifteenIsogenyClassification), which lists the possible values of $(W.c_4)^3/W.\Delta$ for an integral Weierstrass curve with non-vanishing discriminant whose mod $3$ and mod $5$ representations are both reducible in the project's sense.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_fifteenIsogenyJ_of_hauptmodul_memberships.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships {D C u v : ℚ} (hD : D ≠ 0) (h3 : (u + 27) * (u + 3) ^ 3 * D = C * u) (h5 : (v ^ 2 + 10 * v + 5) ^ 3 * D = C * v) : C = -25 / 2 * D ∨ C = -349938025 / 8 * D ∨ C = -121945 / 32 * D ∨ C = 46969655 / 32768 * D := by sorry
