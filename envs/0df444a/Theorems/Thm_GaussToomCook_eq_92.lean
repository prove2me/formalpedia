-- Prove2me | Theorems.Thm_GaussToomCook_eq_92
-- name    : GaussToomCook.eq_92
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:15.492197+00:00
-- url     : https://prove2.me/theorems/263dbf79-4690-42c2-8553-ff9cd73ff5dd
-- title:
--   Eq. (92) — $\det V(T)$ divides $\det V(T;\mathcal J)$
-- statement:
--   Let $T=((x_t,y_t))_{0\le t\le n-1}$ be $n$ points with coordinates in a commutative ring, and let $\mathcal J=\{j_0<j_1<\dots<j_{n-1}\}$ be a set of exponents with $j_c\le D$. Then
--   $$\det V(T)\ \Big|\ \det V(T;\mathcal J),\qquad V(T)=\big[x_t^{\,j}y_t^{\,n-1-j}\big]_{t,\,0\le j\le n-1},\quad V(T;\mathcal J)=\big[x_t^{\,j_c}\,y_t^{\,D-j_c}\big]_{t,c}.$$
--
--   In the paper $D=2k-2$, $\mathcal J\subseteq\{0,\dots,2k-2\}$, $T\subseteq S$ and the ring is $\mathbb Z[i]$; the $V(T;\mathcal J)$ are exactly the $n\times n$ minors of $V(S)$ (eq. (90)). Combined with eq. (91) it shows that every $\det V(T)$ with $|T|=n$ divides $e_1\cdots e_n$ (eq. (93)).
--
--   Differences from the source:
--   - generalization: ℤ[i], exponents 2k − 2 − j with 𝒥 ⊆ {0, …, 2k − 2}, T ⊆ S → any commutative ring, any n points, any bound D ≥ max 𝒥 in place of 2k − 2; reason: the identity is polynomial; R = ℤ[i], D = 2k − 2 and T ⊆ S is an instance.
--   - encoding: V(T) = [x^j y^{|T|−1−j}] (85) for T ⊆ S; 𝒥 a set → Matrix.projVandermonde; 𝒥 a strictly increasing J : Fin n → ℕ with J c ≤ D; reason: a set of exponents in increasing order; J c ≤ D makes the natural-number exponent D − J c the paper's.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.3, proof of Proposition 9.5, eq. (92), p. 32 (PDF p. 34), with eq. (90), p. 31 (PDF p. 33), citing [MM60, Ch. XI]

import Mathlib

namespace GaussToomCook

/-- **Eq. (92): the Vandermonde determinant divides the generalized Vandermonde determinant**,
Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027
submission; sha256 f50b5362…27ad70), §9.3, proof of Proposition 9.5, p. 32 (PDF 34), with (90), p. 31.

For `n` points `(v t, w t)` and a set `J = {J 0 < J 1 < ⋯ < J (n−1)}` of exponents at most `D`, the
determinant of `V(T) = [v_t^j w_t^{n−1−j}]` divides the determinant of
`V(T; J) = [v_t^{J c} w_t^{D − J c}]_{t, c}`.

**Formalization Note.** The paper has `R = ℤ[i]`, `D = 2k − 2`, `J ⊆ {0, …, 2k − 2}`; here `R` is any
commutative ring and `D` any bound on the exponents. The hypothesis `J c ≤ D` makes the natural-number
subtraction `D − J c` the paper's exponent. -/
theorem eq_92 {R : Type*} [CommRing R] {n : ℕ} (v w : Fin n → R) (J : Fin n → ℕ)
    (hJ : StrictMono J) (D : ℕ) (hJD : ∀ c, J c ≤ D) :
    (Matrix.projVandermonde v w).det ∣
      (Matrix.of fun t c => v t ^ J c * w t ^ (D - J c) : Matrix (Fin n) (Fin n) R).det := by sorry

end GaussToomCook
