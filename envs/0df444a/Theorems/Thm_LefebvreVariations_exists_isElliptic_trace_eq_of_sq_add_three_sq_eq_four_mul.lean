-- Prove2me | Theorems.Thm_LefebvreVariations_exists_isElliptic_trace_eq_of_sq_add_three_sq_eq_four_mul
-- name    : LefebvreVariations.exists_isElliptic_trace_eq_of_sq_add_three_sq_eq_four_mul
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:36:46.482168+00:00
-- url     : https://prove2.me/theorems/9e97d9be-38b6-566c-b794-049d4274434e
-- title:
--   Lefebvre's variations, No. 228 — on a theme by Deuring and Waterhouse: a curve over $\mathbb{F}_p$ with trace $t$ whenever $t^2+3m^2=4p$ (the $j=0$ CM family)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $p$ be a prime and let $t,m\in\mathbb{Z}$ with
--
--   $$
--   t^2+3m^2=4p .
--   $$
--
--   Then there exists an elliptic curve $E/\mathbb{F}_p$ with $p+1-\#E(\mathbb{F}_p)=t$. (For $p=2$ there is no solution; for $p=3$ the solutions are $t=\pm3$ and $t=0$.)
--
--   Classical proof: $4p=t^2+3m^2$ means $\pi=(t+m\sqrt{-3})/2\in\mathbb{Z}[\omega]$ has norm $p$. The six twists $y^2=x^3+c$, $c\in\mathbb{F}_p^\times/(\mathbb{F}_p^\times)^6$, of the curve with $j=0$ have Frobenius equal to $\pi$ times a sixth root of unity, so their traces are exactly the numbers $t$ with $t^2+3m^2=4p$ for some $m$, namely $\pm A$ and $\pm(A\pm3B)/2$ where $4p=A^2+3B^2$ (Gauss, cubic Jacobi sums). The statement is the part of Deuring's theorem supplied by the CM field $\mathbb{Q}(\sqrt{-3})$.
--
--   **Formalization Note** The field $\mathbb{F}_p$ is `ZMod p` with `[Fact p.Prime]`. A curve is a `WeierstrassCurve (ZMod p)` (general form, coefficients $a_1,a_2,a_3,a_4,a_6$), and `E.IsElliptic` says its discriminant is a unit, that is nonzero. `E.toAffine.Point` is Mathlib's type of points of $E$: the point at infinity together with the nonsingular affine solutions, so `Nat.card E.toAffine.Point` is $\#E(\mathbb{F}_p)$ including the point at infinity. The trace is written `(p : ℤ) + 1 - Nat.card E.toAffine.Point`. The hypothesis is written with all quantities in `ℤ`.
--
--   **Why this is a Lefebvre variation.** It is one of the two missing steps of a Lean-verified reduction of the open statement PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's existence theorem). In the reduction that statement is split by a case analysis into this family and the complementary pairs $(p,t)$, namely the pairs $(p,t)$ with $t^2-4p\ne-3m^2$ for every integer $m$; the complementary statement is the other open step. This statement is a special case of the base statement, not an ingredient that implies it alone.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). C. F. Gauss, Disquisitiones Arithmeticae (1801), art. 358 on cubic residues and $4p=L^2+27M^2$; Gauss, Theoria residuorum biquadraticorum (1828). K. Ireland and M. Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Chapter 8 (cubic Jacobi sums) and Chapter 18 (point count of $y^2=x^3+D$; cited from memory). J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Chapter V and Appendix A §3. W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521–560, Theorem 4.1 (the statement is a special case of it). Origin of this statement: it is one of the two missing steps of a reduction of PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's theorem over prime fields, p ∤ t): a case split sends the pairs (p, t) of this family to this statement and the complementary pairs to the base statement restricted to them. The case split is verified in Lean; the statements themselves are open.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem exists_isElliptic_trace_eq_of_sq_add_three_sq_eq_four_mul (p : ℕ) [Fact p.Prime] (t m : ℤ)
    (h : t ^ 2 + 3 * m ^ 2 = 4 * p) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
      (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = t := by sorry
end LefebvreVariations
