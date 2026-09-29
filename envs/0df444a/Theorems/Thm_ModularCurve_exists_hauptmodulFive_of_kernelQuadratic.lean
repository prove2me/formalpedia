-- Prove2me | Theorems.Thm_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic
-- name    : ModularCurve.exists_hauptmodulFive_of_kernelQuadratic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/08760e46-7856-5bcc-9250-d606a71d2cc4
-- title:
--   Rational X₀(5) Hauptmodul value from a kernel quadratic
-- statement:
--   Let $A,B,p,q$ be rational numbers such that $4A^3+27B^2\neq 0$ (so $y^2=x^3+Ax+B$ is nonsingular), $p^2-4q\neq 0$ (so $x^2+px+q$ has distinct roots), and the two polynomial relations $2Ap-4B-p^3+6pq=0$ and $A^2-2Aq+4Bp-p^2q+5q^2=0$ hold. The assertion is that there exists a rational number $v\neq 0$ with $$(v^2+10v+5)^3\cdot\bigl(-16(4A^3+27B^2)\bigr)=(-48A)^3\,v,$$ that is, $(v^2+10v+5)^3\,\Delta=c_4^3\,v$ for the discriminant $\Delta=-16(4A^3+27B^2)$ and the invariant $c_4=-48A$ of the curve; equivalently, since $\Delta\neq0$, the $j$-invariant of the curve equals $(v^2+10v+5)^3/v$. The statement is purely an assertion about rational numbers satisfying these four algebraic conditions; no elliptic curve or modular curve occurs in it. The witness produced by the proof is $v=(8B-5p^3+28pq)/(p^3-4pq)$.
--
--   The two hypothesised relations are the classical closure conditions expressing that the roots of $x^2+px+q$ are the abscissae $\{x(T),x(2T)\}$ of a cyclic subgroup of order $5$ of $y^2=x^3+Ax+B$, and the conclusion is Fricke's level-$5$ parametrisation $j=(v^2+10v+5)^3/v$ of the genus-zero curve $X_0(5)$: a curve with a rational $5$-isogeny gives a non-cuspidal rational point of $X_0(5)$. It is used by [`WeierstrassCurve.exists_hauptmodulFive_of_not_modRepIsIrreducible`](thm.html#WeierstrassCurve.exists_hauptmodulFive_of_not_modRepIsIrreducible), which in turn feeds the placing of a curve with reducible mod-$3$ and mod-$5$ representations on $X_0(15)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_hauptmodulFive_of_kernelQuadratic (A B p q : ℚ) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hsep : p ^ 2 - 4 * q ≠ 0) (hg3 : 2 * A * p - 4 * B - p ^ 3 + 6 * p * q = 0) (hg4 : A ^ 2 - 2 * A * q + 4 * B * p - p ^ 2 * q + 5 * q ^ 2 = 0) : ∃ v : ℚ, v ≠ 0 ∧ (v ^ 2 + 10 * v + 5) ^ 3 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = (-48 * A) ^ 3 * v := by sorry
