-- Prove2me | Theorems.Thm_LefebvreVariations_exists_isElliptic_trace_eq_of_class_number_one
-- name    : LefebvreVariations.exists_isElliptic_trace_eq_of_class_number_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:01.48228+00:00
-- url     : https://prove2.me/theorems/0e99ae3e-e2d8-504b-b620-ce3429802b5c
-- title:
--   Lefebvre's variations: a curve over $\mathbb{F}_p$ with trace $t$ whenever $t^2+Dm^2=4p$ for a class-number-one discriminant $-D$ ($D\in\{7,8,11,19,43,67,163\}$)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $D\in\{7,8,11,19,43,67,163\}$ (the absolute values of the seven fundamental discriminants $-7,-8,-11,-19,-43,-67,-163$ of imaginary quadratic fields of class number one other than $-3$ and $-4$), let $p$ be a prime and $t,m\in\mathbb{Z}$ with
--
--   $$
--   t^2+Dm^2=4p .
--   $$
--
--   Then there exists an elliptic curve $E/\mathbb{F}_p$ with $p+1-\#E(\mathbb{F}_p)=t$.
--
--   Classical proof: let $K=\mathbb{Q}(\sqrt{-D})$ and $\mathcal{O}_K$ its ring of integers. The equation says $\pi=(t+m\sqrt{-D})/2\in\mathcal{O}_K$ has norm $p$. The class number is one, so the Hilbert class polynomial is $X-j_D$ with $j_D\in\mathbb{Z}$ ($-3375,\ 8000,\ -32768,\ -884736,\ -884736000,\ -147197952000,\ -262537412640768000$ respectively). Reduce a curve with $j=j_D$ modulo $p$; its Frobenius is a unit multiple of $\pi$ or $\bar\pi$, and a quadratic twist changes the sign, so the trace $t$ occurs (Deuring's lifting and reduction, as used in the CM method of Atkin and Morain).
--
--   **Formalization Note** The field $\mathbb{F}_p$ is `ZMod p` with `[Fact p.Prime]`. A curve is a `WeierstrassCurve (ZMod p)` (general form, coefficients $a_1,a_2,a_3,a_4,a_6$), and `E.IsElliptic` says its discriminant is a unit, that is nonzero. `E.toAffine.Point` is Mathlib's type of points of $E$: the point at infinity together with the nonsingular affine solutions, so `Nat.card E.toAffine.Point` is $\#E(\mathbb{F}_p)$ including the point at infinity. The trace is written `(p : ℤ) + 1 - Nat.card E.toAffine.Point`. The hypothesis is written with all quantities in `ℤ`.
--
--   **Why this is a Lefebvre variation.** It is one of the two missing steps of a Lean-verified reduction of the open statement PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's existence theorem). In the reduction that statement is split by a case analysis into this family and the complementary pairs $(p,t)$, namely the pairs $(p,t)$ with $4p-t^2\ne Dm^2$ for all $D$ in the list and all integers $m$; the complementary statement is the other open step. This statement is a special case of the base statement, not an ingredient that implies it alone.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197–272. W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521–560, Theorem 4.1 (the statement is a special case of it). A. O. L. Atkin and F. Morain, Elliptic curves and primality proving, Math. Comp. 61 (1993), 29–68, §5 (CM method: a root of the Hilbert class polynomial modulo $p$ for $4p=t^2+Dm^2$). D. A. Cox, Primes of the form $x^2+ny^2$, 2nd ed., §13 and Chapter 14 (Hilbert class polynomials; cited from memory), with the list of the class-number-one discriminants from H. M. Stark, A complete determination of the complex quadratic fields of class number one, Michigan Math. J. 14 (1967), 1–27, and A. Baker, Linear forms in the logarithms of algebraic numbers, Mathematika 13 (1966), 204–216. J. H. Silverman, Advanced Topics in the Arithmetic of Elliptic Curves, Chapter II §4–5. Origin of this statement: it is one of the two missing steps of a reduction of PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's theorem over prime fields, p ∤ t): a case split sends the pairs (p, t) of this family to this statement and the complementary pairs to the base statement restricted to them. The case split is verified in Lean; the statements themselves are open.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem exists_isElliptic_trace_eq_of_class_number_one (p : ℕ) [Fact p.Prime] (D : ℕ) (hD : D ∈ ({7, 8, 11, 19, 43, 67, 163} : Finset ℕ))
    (t m : ℤ) (h : t ^ 2 + (D : ℤ) * m ^ 2 = 4 * p) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
      (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = t := by sorry
end LefebvreVariations
