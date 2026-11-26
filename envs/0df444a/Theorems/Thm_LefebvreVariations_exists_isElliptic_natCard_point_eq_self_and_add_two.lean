-- Prove2me | Theorems.Thm_LefebvreVariations_exists_isElliptic_natCard_point_eq_self_and_add_two
-- name    : LefebvreVariations.exists_isElliptic_natCard_point_eq_self_and_add_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:27.105797+00:00
-- url     : https://prove2.me/theorems/0f651e3e-6a86-464a-8a37-613cb7afea9f
-- title:
--   Lefebvre's variations, No. 194 — on a theme by Deuring and Waterhouse: for every prime $p$, elliptic curves over $\mathbb{F}_p$ with exactly $p$ points and with exactly $p+2$ points
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   For every prime $p$ there exist two elliptic curves $E_1,E_2$ over $\mathbb{F}_p$ with
--
--   $$
--   \#E_1(\mathbb{F}_p)=p,\qquad \#E_2(\mathbb{F}_p)=p+2 ,
--   $$
--
--   i.e. with Frobenius traces $+1$ and $-1$. The curve with $\#E_1=p$ is an *anomalous* curve (Frobenius trace $1$; the Smart–Satoh–Araki attack applies to it).
--
--   Classical proof: $t=\pm1$ satisfies $t^2\le4p$ and $p\nmid t$, so $t=\pm1$ is an ordinary trace, with $t^2-4p=1-4p<0$. Deuring's theorem gives the curves; the two signs are related by a quadratic twist (for odd $p$). For small $p$ the curves are explicit; for large $p$ there is no explicit family, which is why anomalous curves are produced in practice by the CM method (Miyaji 1991, Atkin–Morain 1993).
--
--   **Formalization Note** The field $\mathbb{F}_p$ is `ZMod p` with `[Fact p.Prime]`. A curve is a `WeierstrassCurve (ZMod p)` (general form, coefficients $a_1,a_2,a_3,a_4,a_6$), and `E.IsElliptic` says its discriminant is a unit, that is nonzero. `E.toAffine.Point` is Mathlib's type of points of $E$: the point at infinity together with the nonsingular affine solutions, so `Nat.card E.toAffine.Point` is $\#E(\mathbb{F}_p)$ including the point at infinity. The trace is written `(p : ℤ) + 1 - Nat.card E.toAffine.Point`. The hypothesis is written with all quantities in `ℤ`.
--
--   **Why this is a Lefebvre variation.** It is one of the two missing steps of a Lean-verified reduction of the open statement PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's existence theorem). In the reduction that statement is split by a case analysis into this family and the complementary pairs $(p,t)$, namely the pairs $(p,t)$ with $t\notin\{1,-1\}$; the complementary statement is the other open step. This statement is a special case of the base statement, not an ingredient that implies it alone.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521–560, Theorem 4.1 (the statement is the case $t=\pm1$). M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197–272. A. Miyaji, Elliptic curves over $\mathbb{F}_p$ suitable for cryptosystems, Advances in Cryptology – AUSCRYPT '92, LNCS 718, 1993, 479–491, and Elliptic curves suitable for cryptosystems, IEICE Trans. E77-A (1994), 98–104 (anomalous curves $\#E=p$ by the CM method; cited from memory). N. P. Smart, The discrete logarithm problem on elliptic curves of trace one, J. Cryptology 12 (1999), 193–196. A. O. L. Atkin and F. Morain, Elliptic curves and primality proving, Math. Comp. 61 (1993), 29–68. Origin of this statement: it is one of the two missing steps of a reduction of PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd (the ordinary case of Deuring's theorem over prime fields, p ∤ t): a case split sends the pairs (p, t) of this family to this statement and the complementary pairs to the base statement restricted to them. The case split is verified in Lean; the statements themselves are open.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem exists_isElliptic_natCard_point_eq_self_and_add_two (p : ℕ) [Fact p.Prime] :
    (∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = p) ∧
      (∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = p + 2) := by sorry
end LefebvreVariations
