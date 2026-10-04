-- Prove2me | Theorems.Thm_NumberField_Brumer_exists_int_coeffs_vanishing
-- name    : NumberField.Brumer.exists_int_coeffs_vanishing
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:28:09.93396+00:00
-- url     : https://prove2.me/theorems/8d233f61-a565-45b6-af15-c8a5ba5e0fe9
-- title:
--   Brumer's theorem, Lemme 1: integer coefficients of controlled size for the auxiliary function (Siegel's lemma)
-- statement:
--   Let $L$ be a number field of degree $d$, let $a_1,\dots,a_n, c_1,\dots,c_n \in L$, let $k \in \{1,\dots,n\}$ be an index (the pivot) and let $q \ge 0$ be an integer. For $\lambda \in \{0,\dots,N-1\}^n$ put
--   $$u_\lambda = \prod_{i} a_i^{\lambda_i}, \qquad \gamma_i(\lambda) = c_k \lambda_i - c_i \lambda_k \quad (1 \le i \le n),$$
--   and for integers $P(\lambda)$, a multi-index $m \in \mathbb{N}^n$ and $\ell \ge 1$ put
--   $$Q(m, \ell) = \sum_{\lambda} P(\lambda)\, u_\lambda^{\,q\ell} \prod_{i} \gamma_i(\lambda)^{m_i} \in L .$$
--   The statement asserts that there is a constant $C \ge 1$, which depends only on $L, a, c, k, q$, with this property: for all integers $N \ge 1$, $S \ge 0$, $H \ge 0$ with
--   $$2\, d\, (S+1)^{n-1} H \le N^n$$
--   there are integers $P(\lambda)$, not all zero, with
--   $$|P(\lambda)| \le N^n \, C^{\,NH + S}\, N^{S} \quad\text{and}\quad Q(m,\ell) = 0 \ \text{ for all } |m| \le S,\ 1 \le \ell \le H .$$
--
--   **Meaning.** If $\sum_i c_i \log a_i = 0$, then $c_k \log u_\lambda = \sum_i \gamma_i(\lambda) \log a_i$, and $Q(m,\ell)$ is, up to non-zero factors, the partial derivative of order $m$ of the auxiliary function $\sum_\lambda P(\lambda) \prod_i a_i^{\gamma_i(\lambda) z_i}$ at the diagonal point $(q\ell,\dots,q\ell)$. The lemma itself is algebraic: it does not use a place of $L$, a logarithm or the relation.
--
--   **Proof idea.** Since $\gamma_k = 0$, the equations with $m_k > 0$ hold for all $P$. There are at most $(S+1)^{n-1} H$ other equations in $L$. After multiplication by a common denominator and expansion in an integral basis they become at most $d (S+1)^{n-1} H$ linear equations with integer coefficients of size at most $C^{NH+S} N^S$ in the $N^n$ unknowns $P(\lambda)$. Siegel's lemma with at least twice as many unknowns as equations gives a non-zero solution with $|P(\lambda)| \le N^n \cdot (\text{coefficient bound})$.
--
--   **Use.** This is the first step of the proof of `NumberField.Brumer.exists_auxiliary_polynomial`.
--
--   **Formalization Note.** The box is `Fin n → Fin N`; $\lambda_i$ is `(lam i : ℕ)`; $|m| \le S$ is `∑ i, m i ≤ S`; the exponent $n - 1$ is natural subtraction (the existence of `k : Fin n` gives $n \ge 1$). The constant is chosen after $q$, so it can depend on $q$; the exponent of $C$ has $N H$ and not $q N H$. For $H = 0$ there are no equations. The platform has an entrywise Siegel lemma, `Transcendence.siegel_entrywise`; Mathlib has `Int.Matrix.exists_ne_zero_int_vec_norm_le` and the house of an algebraic number (`NumberField.house`).
-- source:
--   B. Rousseau, Séminaire de Théorie des Nombres de Bordeaux 1968-1969, exposé 11, pp. 3-4, Lemme 1 (the construction is from A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204-216); S. Dasgupta, Ranks of matrices of logarithms of algebraic numbers I, arXiv:2303.02037, Lemma 2.3, Lemma 2.4 (Siegel) and Theorem 2.5. Differences from these sources: the box is $\{0,\dots,N-1\}^n$; the exponents are in the homogeneous form $\gamma_i(\lambda) = c_k\lambda_i - c_i\lambda_k$ for a pivot index $k$ (the sources divide by the pivot coefficient and write $\lambda_i + \beta_i\lambda_n$); the constant is existential and the count condition is a hypothesis.

import Mathlib

open NumberField

theorem NumberField.Brumer.exists_int_coeffs_vanishing {L : Type*} [Field L] [NumberField L] (n : ℕ)
    (a c : Fin n → L) (k : Fin n) (q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N S H : ℕ, 0 < N →
      2 * Module.finrank ℚ L * (S + 1) ^ (n - 1) * H ≤ N ^ n →
      ∃ P : (Fin n → Fin N) → ℤ, P ≠ 0 ∧
        (∀ lam, |(P lam : ℝ)| ≤ (N : ℝ) ^ n * C ^ (N * H + S) * (N : ℝ) ^ S) ∧
        ∀ m : Fin n → ℕ, ∑ i, m i ≤ S → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ H →
          ∑ lam : Fin n → Fin N, (P lam : L) * (∏ i, a i ^ (lam i : ℕ)) ^ (q * ℓ) *
            ∏ i, (c k * ((lam i : ℕ) : L) - c i * ((lam k : ℕ) : L)) ^ m i = 0 := by sorry
