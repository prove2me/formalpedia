-- Prove2me | Theorems.Thm_LefebvreVariations_exists_isElliptic_trace_eq_of_class_number_two
-- name    : LefebvreVariations.exists_isElliptic_trace_eq_of_class_number_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:45.494611+00:00
-- url     : https://prove2.me/theorems/b3a753bf-13ed-4ae2-93a4-d19bfd5bc38b
-- title:
--   Lefebvre's variations, No. 236 — on a theme by Deuring and Waterhouse: a curve over $\mathbb{F}_p$ with trace $t$ whenever $t^2+Dm^2=4p$ for a class-number-two fundamental discriminant $-D$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $D$ be one of the eighteen integers $15,20,24,35,40,51,52,88,91,115,123,148,187,232,235,267,403,427$ (the absolute values of the fundamental discriminants of imaginary quadratic fields of class number two), let $p$ be a prime and $t,m\in\mathbb{Z}$ with
--
--   $$
--   t^2+Dm^2=4p .
--   $$
--
--   Then there exists an elliptic curve $E/\mathbb{F}_p$ with $p+1-\#E(\mathbb{F}_p)=t$.
--
--   Classical proof: with $K=\mathbb{Q}(\sqrt{-D})$, $\pi=(t+m\sqrt{-D})/2\in\mathcal{O}_K$ has norm $p$, so the prime $(\pi)$ is principal and $p$ splits completely in the Hilbert class field $H$ of $K$. The Hilbert class polynomial $H_{-D}(X)\in\mathbb{Z}[X]$ has degree $h(-D)=2$, and a degree-two polynomial that splits modulo $p$ has a root $j\in\mathbb{F}_p$ (for $p\nmid\operatorname{disc}$). A curve over $\mathbb{F}_p$ with this $j$ has Frobenius $\pm\pi$ or $\pm\bar\pi$, and a quadratic twist fixes the sign. This is the first case after class number one where the root exists only because the class polynomial splits.
--
--   **Formalization Note** The field $\mathbb{F}_p$ is `ZMod p` with `[Fact p.Prime]`. A curve is a `WeierstrassCurve (ZMod p)` (general form, coefficients $a_1,a_2,a_3,a_4,a_6$), and `E.IsElliptic` says its discriminant is a unit, that is nonzero. `E.toAffine.Point` is Mathlib's type of points of $E$: the point at infinity together with the nonsingular affine solutions, so `Nat.card E.toAffine.Point` is $\#E(\mathbb{F}_p)$ including the point at infinity. The trace is written `(p : ℤ) + 1 - Nat.card E.toAffine.Point`. The hypothesis is written with all quantities in `ℤ`.
--
--   **Why this is a Lefebvre variation.** It is one of the two missing steps of a Lean-verified reduction of the open statement PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's existence theorem). In the reduction that statement is split by a case analysis into this family and the complementary pairs $(p,t)$, namely the pairs $(p,t)$ with $4p-t^2\ne Dm^2$ for all $D$ in the list and all integers $m$; the complementary statement is the other open step. This statement is a special case of the base statement, not an ingredient that implies it alone.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197–272. W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521–560, Theorem 4.1 (the statement is a special case of it). D. A. Cox, Primes of the form $x^2+ny^2$, 2nd ed., §13 and §14 (a prime is $x^2+ny^2$ iff it splits completely in the ring class field; Hilbert class polynomials). A. O. L. Atkin and F. Morain, Elliptic curves and primality proving, Math. Comp. 61 (1993), 29–68, §5. The class-number-two list: H. L. Montgomery and P. J. Weinberger, Notes on small class numbers, Acta Arith. 24 (1973/74), 529–542 (18 fundamental discriminants, with Baker 1971 and Stark 1971). Origin of this statement: it is one of the two missing steps of a reduction of PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's theorem over prime fields, p ∤ t): a case split sends the pairs (p, t) of this family to this statement and the complementary pairs to the base statement restricted to them. The case split is verified in Lean; the statements themselves are open.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem exists_isElliptic_trace_eq_of_class_number_two (p : ℕ) [Fact p.Prime] (D : ℕ) (hD : D ∈ ({15, 20, 24, 35, 40, 51, 52, 88, 91, 115, 123, 148, 187, 232, 235, 267, 403, 427} : Finset ℕ))
    (t m : ℤ) (h : t ^ 2 + (D : ℤ) * m ^ 2 = 4 * p) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
      (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = t := by sorry
end LefebvreVariations
