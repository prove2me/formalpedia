-- Prove2me | Theorems.Thm_IntMul_HvdH_agarwal_cooley_poly
-- name    : IntMul.HvdH.agarwal_cooley_poly
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:39:00.124042+00:00
-- url     : https://prove2.me/theorems/b457d209-db92-4be6-b119-c64d29124845
-- title:
--   Agarwal–Cooley: a short product is a multidimensional cyclic convolution
-- statement:
--   **Agarwal–Cooley reindexing.** Let $s_1,\dots,s_d\ge1$ be pairwise coprime, $S=s_1\cdots s_d$, and let $\varepsilon:\mathbb Z/S\to\prod_i\mathbb Z/s_i$ be the Chinese-remainder isomorphism $k\mapsto(k\bmod s_1,\dots,k\bmod s_d)$. Let $R$ be a commutative ring and $F,G\in R[x]$ with $\deg F+\deg G<S$. Then for every $0\le j<S$,
--   $$[x^j]\,(FG)=\sum_{b\in\prod_i\mathbb Z/s_i}[x^{\varepsilon^{-1}(b)}]F\cdot[x^{\varepsilon^{-1}(\varepsilon(j)-b)}]G,$$
--   where exponents in $\mathbb Z/S$ are read as their representatives in $[0,S)$.
--
--   So the coefficients of $FG$ are the entries of the $d$-dimensional cyclic convolution of the arrays $F'=F\circ\varepsilon^{-1}$ and $G'=G\circ\varepsilon^{-1}$. These are steps (1)–(2) of Proposition 5.4: since $\deg H<S$, the product may be computed modulo $x^S-1$, and the ring isomorphism $\mathbb Z[x]/(x^S-1)\cong\mathbb Z[x_1,\dots,x_d]/(x_i^{s_i}-1)$, $x\mapsto x_1\cdots x_d$, is a relabelling of coefficients.
--
--   **Formalization Note** $\varepsilon$ is Mathlib's `ZMod.prodEquivPi`, and $\deg$ is `natDegree` (so $\deg 0=0$).
-- source:
--   D. Harvey and J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193 (2021), no. 2, 563–617, https://doi.org/10.4007/annals.2021.193.2.4, §5.3 proof of Proposition 5.4, steps (1)–(2) (deg H < S, so it suffices to compute F G mod x^S − 1; the Agarwal–Cooley isomorphism Z[x]/(x^S−1) ≅ Z[x_1,…,x_d]/(x_i^{s_i}−1) sending x to x_1⋯x_d, for pairwise coprime s_i); R. Agarwal and J. Cooley, New algorithms for digital convolution, IEEE Trans. ASSP 25 (1977)

import Mathlib
open Polynomial

namespace IntMul.HvdH

theorem agarwal_cooley_poly {d : ℕ} (s : Fin d → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (Function.onFun Nat.Coprime s)) {R : Type} [CommRing R] (F G : R[X])
    (hdeg : F.natDegree + G.natDegree < ∏ i, s i) (j : ℕ) (hj : j < ∏ i, s i) :
    (F * G).coeff j =
      ∑ b : Π i, ZMod (s i),
        F.coeff ((ZMod.prodEquivPi s hcop).symm b).val *
          G.coeff ((ZMod.prodEquivPi s hcop).symm (ZMod.prodEquivPi s hcop j - b)).val := by sorry

end IntMul.HvdH
