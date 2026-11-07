-- Prove2me | Theorems.Thm_LineVsPoint_lemma_2_6
-- name    : LineVsPoint.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:03:03.628269+00:00
-- url     : https://prove2.me/theorems/42c95c9c-6e66-4abd-902a-13932336b9a9
-- title:
--   Lemma 2.6 — Newton–Hensel lifting, two-variable and one-variable forms
-- statement:
--   **Lemma 2.6** (Newton iteration; [HKSS24, Lemma 2.10]). Let $\mathbb F_q$ be a finite field.
--
--   1. Let $B\in\mathbb F_q[X,Y,Z]$ and $\alpha\in\mathbb F_q$ satisfy $B(0,0,\alpha)=0$ and $B_Z(0,0,\alpha)\ne 0$. For every integer $k\ge 0$ there is a unique polynomial $\Phi_k\in\mathbb F_q[X,Y]$ of total degree at most $k$ such that
--   $$
--   \Phi_k(0,0)=\alpha,\qquad B(X,Y,\Phi_k(X,Y))\equiv 0\pmod{(X,Y)^{k+1}} .
--   $$
--   2. (*One-variable form.*) The same holds for $B\in\mathbb F_q[T,Z]$ with one variable $T$ in place of $X,Y$: if $B(0,\alpha)=0$ and $B_Z(0,\alpha)\ne0$, then for every $k\ge0$ there is a unique $\varphi\in\mathbb F_q[T]$ of degree at most $k$ with $\varphi(0)=\alpha$ and $B(T,\varphi(T))\equiv 0\pmod{T^{k+1}}$.
--
--   $B_Z$ is the formal partial derivative in $Z$. The uniqueness in the one-variable form is what propagates a single polynomial through a connected component in Lemmas 2.7 and 3.5.
--
--   Differences from the source:
--   - encoding: unique polynomial of total degree at most k with the two properties → ∃! over polynomials, of the conjunction (degree ≤ k, value α at 0, the congruence); reason: the same uniqueness class
--   - encoding: B(X, Y, Φ) ≡ 0 (mod (X, Y)^{k+1}); in one variable, mod T^{k+1} → membership of bind₁ ![X 0, X 1, Φ] B in (Ideal.span {X 0, X 1})^(k+1); divisibility of aeval ![X, φ] B by X^(k+1); reason: the ideal (T)^{k+1} of F[T] is the set of multiples of T^{k+1}
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.6 and the sentence after it, p.14

import Mathlib

set_option autoImplicit false

universe u

namespace LineVsPoint

open MvPolynomial in
/-- **Lemma 2.6** (Newton–Hensel lifting) *and its one-variable form.* *Let `B ∈ F_q[X, Y, Z]` and
`α ∈ F_q` satisfy `B(0, 0, α) = 0`, `B_Z(0, 0, α) ≠ 0`. For every integer `k ≥ 0`, there is a
unique polynomial `Φ_k ∈ F_q[X, Y]` of total degree at most `k` such that `Φ_k(0, 0) = α`,
`B(X, Y, Φ_k(X, Y)) ≡ 0 (mod (X, Y)^{k+1})`. The same statement, with the same proof, holds for
`B ∈ F_q[T, Z]` with one variable `T` in place of `X, Y`; we call this the one-variable form of
Lemma 2.6.* Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the
Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 2.6, p.14.

**Formalization Note.** The first conjunct is the two-variable lemma: `X, Y, Z` are the variables
`0, 1, 2`, `B_Z = ∂B/∂Z` is `pderiv 2 B`, `B(X, Y, Φ)` is `bind₁ ![X 0, X 1, Φ] B`, and
"`≡ 0 (mod (X, Y)^{k+1})`" is membership in the `(k+1)`-st power of the ideal `(X, Y)`. The second
conjunct is the one-variable form: `B ∈ F[T, Z]` with `T, Z` the variables `0, 1`, `φ ∈ F[T]` a
univariate polynomial of degree `≤ k`, and "`≡ 0 (mod T^{k+1})`" is divisibility by `T^{k+1}`.
"Unique" is `∃!` among polynomials of degree `≤ k` with the two properties. -/
theorem lemma_2_6 :
    ∀ (F : Type u) [Field F] [Fintype F],
      (∀ (B : MvPolynomial (Fin 3) F) (α : F), eval ![0, 0, α] B = 0 →
        eval ![0, 0, α] (pderiv 2 B) ≠ 0 →
        ∀ k : ℕ, ∃! Φ : MvPolynomial (Fin 2) F, Φ.totalDegree ≤ k ∧ eval 0 Φ = α ∧
          bind₁ ![X 0, X 1, Φ] B ∈ (Ideal.span {X 0, X 1} : Ideal (MvPolynomial (Fin 2) F)) ^ (k + 1)) ∧
      (∀ (B : MvPolynomial (Fin 2) F) (α : F), eval ![0, α] B = 0 →
        eval ![0, α] (pderiv 1 B) ≠ 0 →
        ∀ k : ℕ, ∃! φ : Polynomial F, φ.natDegree ≤ k ∧ φ.eval 0 = α ∧
          Polynomial.X ^ (k + 1) ∣ aeval ![Polynomial.X, φ] B) := by sorry

end LineVsPoint
