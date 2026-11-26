-- Prove2me | Theorems.Thm_LefebvreVariations_exists_isElliptic_trace_eq_two_mul_of_sq_add_sq
-- name    : LefebvreVariations.exists_isElliptic_trace_eq_two_mul_of_sq_add_sq
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:36:21.599073+00:00
-- url     : https://prove2.me/theorems/79102283-ecf0-5316-83bd-eca1b69f3d64
-- title:
--   Lefebvre's variations, No. 187 — on a theme by Deuring and Waterhouse: a curve over $\mathbb{F}_p$ with trace $2a$ whenever $p=a^2+b^2$ (the $j=1728$ CM family)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $p$ be a prime and let $a,b\in\mathbb{Z}$ with $a^2+b^2=p$ (so $p=2$ or $p\equiv1\pmod 4$, and $a,b$ may be taken of either sign and in either order). Then there exists an elliptic curve $E/\mathbb{F}_p$ with
--
--   $$
--   \#E(\mathbb{F}_p)=p+1-2a ,
--   $$
--
--   that is, with Frobenius trace $t=2a$. Since $a$ and $b$ may be swapped and negated, this gives the four traces $\pm2a,\pm2b$.
--
--   Classical proof: $p=\pi\bar\pi$ in $\mathbb{Z}[i]$ with $\pi=a+bi$; the twists $y^2=x^3-cx$, $c\in\mathbb{F}_p^\times$, of the curve with $j=1728$ have Frobenius $\pi$ times a unit, so their traces are $\pm2a,\pm2b$ (Gauss; the point count is a quartic Jacobsthal / Jacobi sum). The full statement of Deuring's theorem is about all $t$ with $t^2\le4p$; this is the part that the single CM field $\mathbb{Q}(i)$ gives, here $t^2-4p=-4b^2$.
--
--   **Formalization Note** The field $\mathbb{F}_p$ is `ZMod p` with `[Fact p.Prime]`. A curve is a `WeierstrassCurve (ZMod p)` (general form, coefficients $a_1,a_2,a_3,a_4,a_6$), and `E.IsElliptic` says its discriminant is a unit, that is nonzero. `E.toAffine.Point` is Mathlib's type of points of $E$: the point at infinity together with the nonsingular affine solutions, so `Nat.card E.toAffine.Point` is $\#E(\mathbb{F}_p)$ including the point at infinity. The trace is written `(p : ℤ) + 1 - Nat.card E.toAffine.Point`. The hypothesis is written with all quantities in `ℤ`.
--
--   **Why this is a Lefebvre variation.** It is one of the two missing steps of a Lean-verified reduction of the open statement PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's existence theorem). In the reduction that statement is split by a case analysis into this family and the complementary pairs $(p,t)$, namely the pairs $(p,t)$ such that $t\ne 2a$ for every representation $p=a^2+b^2$ (that is, $t^2-4p\neq -4b^2$ for all integers $b$); the complementary statement is the other open step. This statement is a special case of the base statement, not an ingredient that implies it alone.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). C. F. Gauss, Disquisitiones Arithmeticae (1801) and Theoria residuorum biquadraticorum (1828) (cubic and quartic character sums and $p=a^2+b^2$). E. Jacobsthal, Über die Darstellung der Primzahlen der Form $4n+1$ als Summe zweier Quadrate, J. reine angew. Math. 132 (1907), 238–245. K. Ireland and M. Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Chapter 18 (the point count of $y^2=x^3-Dx$ over $\mathbb{F}_p$, $p\equiv1\pmod 4$, through the quartic residue symbol of the primary prime $a+bi$; cited from memory). J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Appendix A §3 and Chapter V. W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521–560, Theorem 4.1 (the statement is a special case of it). Origin of this statement: it is one of the two missing steps of a reduction of PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's theorem over prime fields, p ∤ t): a case split sends the pairs (p, t) of this family to this statement and the complementary pairs to the base statement restricted to them. The case split is verified in Lean; the statements themselves are open.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem exists_isElliptic_trace_eq_two_mul_of_sq_add_sq (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (hab : a ^ 2 + b ^ 2 = p) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
      (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = 2 * a := by sorry
end LefebvreVariations
