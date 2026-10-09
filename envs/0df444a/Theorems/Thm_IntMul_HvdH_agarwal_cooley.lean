-- Prove2me | Theorems.Thm_IntMul_HvdH_agarwal_cooley
-- name    : IntMul.HvdH.agarwal_cooley
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T01:44:17.129978+00:00
-- url     : https://prove2.me/theorems/dcee2eb8-8b5e-4767-af4a-38d12e938a08
-- title:
--   HvdH Proposition 5.4, step (2) — Agarwal–Cooley isomorphism $\mathbb Z[x]/(x^S-1)\cong\mathbb Z[x_1,\dots,x_d]/(x_i^{s_i}-1)$
-- statement:
--   Let $d\ge0$ and let $s_1,\dots,s_d\ge1$ be pairwise coprime integers, $S:=s_1\cdots s_d$. Then there is a ring isomorphism
--   $$\mathbb Z[x]/(x^S-1)\;\xrightarrow{\ \sim\ }\;\mathcal A:=\mathbb Z[x_1,\dots,x_d]/(x_1^{s_1}-1,\dots,x_d^{s_d}-1)$$
--   sending the class of $x$ to the class of $x_1x_2\cdots x_d$.
--
--   This is the isomorphism "induced by the Chinese remainder theorem" used in step (2) of the proof of Proposition 5.4 to turn a one-dimensional cyclic convolution of length $S=s_1\cdots s_d$ into a $d$-dimensional one. (Under it, $x^k\mapsto\prod_ix_i^{k\bmod s_i}$.)
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), proof of Proposition 5.4, step (2) 'Reduce to d-dimensional convolution over Z', p. 41; R. C. Agarwal, J. W. Cooley, New algorithms for digital convolution, IEEE Trans. ASSP 25 (1977).

import Mathlib

namespace IntMul.HvdH

theorem agarwal_cooley (d : ℕ) (s : Fin d → ℕ) (hs : ∀ i, 1 ≤ s i)
    (hcop : Pairwise fun i j => Nat.Coprime (s i) (s j)) :
    ∃ e : (Polynomial ℤ ⧸ Ideal.span {(Polynomial.X ^ (∏ i, s i) - 1 : Polynomial ℤ)}) ≃+*
        (MvPolynomial (Fin d) ℤ ⧸
          Ideal.span (Set.range fun i => (MvPolynomial.X i ^ s i - 1 : MvPolynomial (Fin d) ℤ))),
      e (Ideal.Quotient.mk _ Polynomial.X) = Ideal.Quotient.mk _ (∏ i, MvPolynomial.X i) := by
  sorry

end IntMul.HvdH
