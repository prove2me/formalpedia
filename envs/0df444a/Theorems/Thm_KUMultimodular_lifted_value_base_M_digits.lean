-- Prove2me | Theorems.Thm_KUMultimodular_lifted_value_base_M_digits
-- name    : KUMultimodular.lifted_value_base_M_digits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:02:53.238991+00:00
-- url     : https://prove2.me/theorems/6b06087c-d7bc-45c1-b776-2b47f0b2f987
-- title:
--   Proof of Theorem 4.4: $\tilde f(\tilde\alpha_i)$ is recovered from its value at $Z=M$ modulo $r'$ (corrected: $m \ge 1$)
-- statement:
--   Let $r \ge 1$, let $E \in (\mathbb Z/r\mathbb Z)[Z]$ be monic of degree $e$, $R = (\mathbb Z/r\mathbb Z)[Z]/(E(Z))$, $m \ge 1$, $d \in \mathbb N$, let $f \in R[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable and let $a \in R^m$. Lift every coefficient of $f$ and every coordinate of $a$ to a polynomial in $\mathbb N[Z]$ of degree at most $e-1$ with coefficients in $\{0,\dots,r-1\}$, and let $P = \tilde f(\tilde a) \in \mathbb N[Z]$. With
--   $$M = d^m (e(r-1))^{(d-1)m+1} + 1, \qquad r' = M^{(e-1)dm+1},$$
--   1. $\deg P \le (e-1)dm$;
--   2. $P(1) \le M - 1$;
--   3. every coefficient of $P$ is at most $M-1$;
--   4. for every $i \ge 0$, the $i$-th base-$M$ digit $\lfloor (P(M) \bmod r')/M^i \rfloor \bmod M$ equals the coefficient of $Z^i$ in $P$; so the polynomial $Q$ of Step 4 (degree $\le (e-1)dm$, coefficients in $\{0,\dots,M-1\}$, $Q(M) \equiv P(M) \pmod{r'}$) is $P$;
--   5. the reduction of $P$ modulo $r$ and $E(Z)$ is $f(a)$.
--
--   This is the correctness half of Theorem 4.4: Algorithm MULTIMODULAR over $\mathbb Z/r'\mathbb Z$ returns $P(M) \bmod r'$, and Step 4 turns it back into $f(\alpha_i)$.
--
--   **Formalization Note** $R$ is `AdjoinRoot E`, the lift of $x$ is `liftPoly hE x` (from `AdjoinRoot.modByMonicHom`), and $M$, $r'$ are `bigM r e m d`, `rPrime r e m d` with truncated $e - 1$ and $d - 1$ (which agree with the paper for $e, d \ge 1$; for $e = 0$ or $d = 0$ every lift or $f$ is $0$).
--
--   Differences from the source:
--   - correction: all m (including m = 0) → 1 ≤ m; reason: counterexample: r = 2, E = Z² + Z + 1 (e = 2), m = 0, d = 1, f = Z: P = Z has degree 1 > (e − 1)dm = 0, and r' = M = 3, so Step 4 returns the digit 3 mod 3 = 0 ≠ Z; the degree bound needs (e−1)(m(d−1)+1) ≤ (e−1)dm
--   - encoding: f̃(α̃_i) ∈ ℤ[Z] with nonnegative coefficients → P ∈ ℕ[Z]; reason: the lifts have coefficients in {0, …, r−1}; same polynomial
--   - encoding: the polynomials f̃(α̃_i) and Q_i coincide → the base-M digits of P(M) mod r' are the coefficients of P (for every index); reason: Q_i is by definition the polynomial whose coefficients are the (e−1)dm + 1 base-M digits of β_i ≡ P(M) (mod r'); the digit statement is the coincidence for every coefficient
--   - encoding: R = (ℤ/rℤ)[Z]/(E(Z)) with r arbitrary → AdjoinRoot E over ZMod r with 0 < r; reason: ZMod 0 = ℤ is not ℤ/rℤ for a finite ring; same instances otherwise
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), proof of Theorem 4.4, p. 15 (first paragraph)

import Mathlib
import Definitions.Def_KUMultimodular_densePoly
import Definitions.Def_KUMultimodular_multimodularExt

namespace KUMultimodular

/-- **The base-`M` coincidence in the proof of Theorem 4.4** (Kedlaya–Umans, Dagstuhl Seminar
Proceedings 08381 (2008), p. 15). Let `R = (ℤ/rℤ)[Z]/(E(Z))` with `E` monic of degree `e`, let
`m ≥ 1`, let `f` have coefficient table `coef` (degree at most `d - 1` in each variable) and let
`a ∈ R^m`. Let `P = f̃(ã) ∈ ℕ[Z]` be the value of the lifted polynomial at the lifted point
(coefficients and coordinates lifted to polynomials of degree `≤ e - 1` with coefficients in
`{0, …, r-1}`), `M = d^m (e(r-1))^{(d-1)m+1} + 1` and `r' = M^{(e-1)dm+1}`. Then
1. `deg P ≤ (e-1)dm`;
2. `P(1) ≤ d^m (e(r-1))^{(d-1)m+1} = M - 1`, and every coefficient of `P` lies in `{0, …, M-1}`;
3. the `i`-th base-`M` digit of `P(M) mod r'` is the `i`-th coefficient of `P`, for every `i`
   (so Step 4's polynomial `Q_i` equals `P`);
4. the reduction of `P` modulo `r` and `E(Z)` is `f(a)`. -/
theorem lifted_value_base_M_digits {r : ℕ} (hr : 0 < r) (E : Polynomial (ZMod r)) (hE : E.Monic)
    {m d : ℕ} (hm : 1 ≤ m) (coef : (Fin m → Fin d) → AdjoinRoot E) (a : Fin m → AdjoinRoot E) :
    (∑ k, liftPoly hE (coef k) * ∏ j, liftPoly hE (a j) ^ (k j : ℕ)).natDegree
        ≤ (E.natDegree - 1) * d * m ∧
      (∑ k, liftPoly hE (coef k) * ∏ j, liftPoly hE (a j) ^ (k j : ℕ)).eval 1
        ≤ bigM r E.natDegree m d - 1 ∧
      (∀ i, (∑ k, liftPoly hE (coef k) * ∏ j, liftPoly hE (a j) ^ (k j : ℕ)).coeff i
        ≤ bigM r E.natDegree m d - 1) ∧
      (∀ i, (∑ k, liftPoly hE (coef k) * ∏ j, liftPoly hE (a j) ^ (k j : ℕ)).eval
          (bigM r E.natDegree m d) % rPrime r E.natDegree m d
            / bigM r E.natDegree m d ^ i % bigM r E.natDegree m d
          = (∑ k, liftPoly hE (coef k) * ∏ j, liftPoly hE (a j) ^ (k j : ℕ)).coeff i) ∧
      AdjoinRoot.mk E ((∑ k, liftPoly hE (coef k) * ∏ j, liftPoly hE (a j) ^ (k j : ℕ)).map
          (Nat.castRingHom (ZMod r)))
        = MvPolynomial.eval a (densePoly coef) := by sorry

end KUMultimodular
