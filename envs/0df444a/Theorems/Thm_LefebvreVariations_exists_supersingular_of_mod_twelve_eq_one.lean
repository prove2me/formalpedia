-- Prove2me | Theorems.Thm_LefebvreVariations_exists_supersingular_of_mod_twelve_eq_one
-- name    : LefebvreVariations.exists_supersingular_of_mod_twelve_eq_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:24:20.185519+00:00
-- url     : https://prove2.me/theorems/2f034e04-b4a8-422f-ab53-8cdbbbd13cad
-- title:
--   Lefebvre's variations, No. 21 — on a theme by Deuring: a supersingular elliptic curve over $\mathbb{F}_p$ for every prime $p \equiv 1 \pmod{12}$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the one case of Deuring's supersingular existence theorem over prime fields that no explicit curve with complex multiplication by $\mathbb{Z}[i]$ or $\mathbb{Z}[\omega]$ covers.
--
--   Let $p$ be a prime with $p \equiv 1 \pmod{12}$. Then there exists an elliptic curve $E$ over $\mathbb{F}_p$, given by a Weierstrass equation
--
--   $$
--   E:\; y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6, \qquad a_i \in \mathbb{F}_p,\ \Delta(E) \ne 0,
--   $$
--
--   with exactly
--
--   $$
--   \#E(\mathbb{F}_p) = p + 1
--   $$
--
--   points, counting the point at infinity. Equivalently, the trace of Frobenius $t = p + 1 - \#E(\mathbb{F}_p)$ is $0$. Since $p \ge 13$, the Hasse bound $|t| \le 2\sqrt{p} < p$ shows that this is the same as asking for a supersingular elliptic curve whose $j$-invariant lies in $\mathbb{F}_p$.
--
--   For the other primes such a curve is explicit: $y^2 = x^3 - x$ has $p + 1$ points when $p \equiv 3 \pmod 4$, $y^2 = x^3 + 1$ has $p + 1$ points when $p \equiv 2 \pmod 3$, and $y^2 + y = x^3$ has $3$ points over $\mathbb{F}_2$. The primes $p \equiv 1 \pmod{12}$ are exactly those left over. For them the classical proof goes through complex multiplication. Reduce modulo a prime above $p$ a curve with complex multiplication by an order of discriminant $-4p$ (or $-p$), in which $p$ ramifies. The number of $\mathbb{F}_p$-isomorphism classes of curves with trace $0$ is the Kronecker class number $H(-4p) > 0$. No finite list of explicit CM curves suffices: the primes $15073$, $18313$, $38833, \dots \equiv 1 \pmod{12}$ split in all nine imaginary quadratic fields of class number one, so none of the thirteen rational CM $j$-invariants is supersingular there.
--
--   **Formalization Note** The field $\mathbb{F}_p$ is `ZMod p` with `[Fact p.Prime]`. A curve is a `WeierstrassCurve (ZMod p)` (general form with coefficients $a_1, a_2, a_3, a_4, a_6$), and `E.IsElliptic` says its discriminant is a unit, that is nonzero. `E.toAffine.Point` is Mathlib's type of points of $E$: the point at infinity together with the nonsingular affine solutions. On an elliptic curve every affine solution is nonsingular, so `Nat.card E.toAffine.Point` is $\#E(\mathbb{F}_p)$ including the point at infinity. The congruence is written `p % 12 = 1`.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `PrescribedPointCount.exists_isElliptic_trace_eq_of_dvd` (Deuring's existence theorem for supersingular traces over $\mathbb{F}_p$). For $p \equiv 2 \pmod 3$ and $p \equiv 3 \pmod 4$, explicit CM curves give trace $0$, and the traces $\pm p$ over $\mathbb{F}_2$, $\mathbb{F}_3$ are checked directly. What is left is the single case $p \equiv 1 \pmod{12}$ with trace $0$, which is this statement. It is a special case of the base statement, and the base statement follows from it together with the proved cases.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197–272 (existence of supersingular curves over F_p via reduction of CM curves). W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521–560, Theorem 4.1 (the trace t = 0 occurs over every prime field). R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183–211, §4 (the number of F_q-isomorphism classes with trace t is the Kronecker class number H(t^2 − 4q); for t = 0, q = p this is H(−4p) > 0). J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Examples V.4.4 and V.4.5 (y^2 = x^3 + 1 for p ≡ 2 mod 3 and y^2 = x^3 + x for p ≡ 3 mod 4 are supersingular). C. Delfs and S. D. Galbraith, Computing isogenies between supersingular elliptic curves over F_p, Des. Codes Cryptogr. 78 (2016), 425–440, §2 (counts of F_p-rational supersingular j-invariants by class numbers). Origin of this statement: it is the missing step of a reduction of PrescribedPointCount.exists_isElliptic_trace_eq_of_dvd (Deuring's theorem over prime fields, supersingular case p | t). In that reduction everything else is proved in Lean: p | t and t^2 ≤ 4p force t = 0, or p ∈ {2, 3} and t = ±p; the count #E = 1 + #{affine solutions} for an elliptic curve and #E = q + 1 + Σ_x χ(x^3 + ax + b) for short Weierstrass curves in odd characteristic; y^2 = x^3 − x has p + 1 points for p ≡ 3 mod 4 (the character sum is odd under x ↦ −x) and y^2 = x^3 + 1 has p + 1 points for p ≡ 2 mod 3 (x ↦ x^3 is a bijection); the six remaining small cases over F_2 and F_3 (traces 0, ±2 over F_2 and ±3 over F_3) are explicit curves counted by decide. Only the primes p ≡ 1 mod 12 with t = 0 are left, and they are exactly this statement.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem exists_supersingular_of_mod_twelve_eq_one (p : ℕ) [Fact p.Prime] (hp : p % 12 = 1) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = p + 1 := by sorry
end LefebvreVariations
