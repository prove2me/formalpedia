-- Prove2me | Theorems.Thm_NetServicePricing_fact_6
-- name    : NetServicePricing.fact_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:13.864426+00:00
-- url     : https://prove2.me/theorems/df2b98c7-855c-41cb-8f50-592d93380f66
-- title:
--   Fact 6 — equal row sums give $\lambda_1(A)=\bar A$ with eigenvector $\mathbf 1/\sqrt n$ (corrected: $A$ nonnegative)
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix with nonnegative entries, $n\ge1$, whose row sums are all equal:
--
--   $$\sum_{j=1}^n A_{ij}=\bar A\qquad(1\le i\le n).$$
--
--   Then
--
--   1. $A\mathbf 1=\bar A\,\mathbf 1$ and $\bar A$ is an eigenvalue of $A$;
--   2. every eigenvalue of $A$ is at most $\bar A$, so $\lambda_1(A)=\bar A$;
--   3. there is an orthonormal eigenbasis $v_1,\dots,v_n$ of $A$ in which the eigenvector for $\bar A$ is $v_1=(1,1,\dots,1)/\sqrt n$, and $\langle v_1,v_i\rangle=0$ for every other basis vector $v_i$.
--
--   In the paper it identifies the top eigenpair of every balanced network: all balanced networks with average degree $\mathcal D$ have $\lambda_1=\mathcal D$ and $v_1=\mathbf 1/\sqrt n$, with all other eigenvectors orthogonal to $\mathbf 1$.
--
--   Differences from the source:
--   - correction: A symmetric (preamble of EC.1) → A symmetric and entrywise nonnegative; reason: the printed statement is false: A = [[1, −2], [−2, 1]] is symmetric with both row sums −1 but has eigenvalues 3 and −1, so λ₁(A) = 3 ≠ Ā; the paper applies Fact 6 only to networks, which are nonnegative
--   - reading: λ₁(A) = Ā with v₁(A) = (1,…,1)/√n → Ā is an eigenvalue, every eigenvalue is ≤ Ā, and some orthonormal eigenbasis has (1,…,1)/√n as its eigenvector for Ā at an index i₀, orthogonal to the others; reason: when Ā is a multiple eigenvalue "the" eigenvector v₁(A) depends on the chosen basis
--   - encoding: eigenvalues λ₁(A) ≥ … ≥ λₙ(A) of an n × n matrix → 0 < n; reason: λ₁(A) exists only for n ≥ 1; the hypothesis excludes only the undefined case
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Fact 6, p.ec2; preamble of EC.1, p.ec1

import Mathlib

open Matrix

namespace NetServicePricing

/-- **Fact 6 (equal row sums), corrected: `A` nonnegative.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Fact 6, p.ec2: "Suppose that the row sum of all rows in matrix A are equal, i.e.,
∑_{j=1}^n Aij = Ā, for 1 ≤ i ≤ n. Then λ1(A) = Ā, with v1(A) = (1,1,...,1)/√n. Further,
⟨v1,vi⟩ = 0, for 2 ≤ i ≤ n.", where by the preamble of EC.1 (p.ec1) `A` is symmetric and
"λ1(A) ≥ λ2(A) ≥ ... ≥ λn(A)".

For a symmetric, entrywise nonnegative `A` (with `n ≥ 1`) whose row sums all equal `Ā`:
`A𝟏 = Ā𝟏`, `Ā` is an eigenvalue of `A` and every eigenvalue of `A` is at most `Ā` (so
`λ₁(A) = Ā`), and some orthonormal eigenbasis of `A` has `𝟏/√n` as its eigenvector for `Ā`, all
other basis vectors being orthogonal to it.

**Formalization Note** Correction: the printed statement is false for a general symmetric `A`:
`A = [[1, −2], [−2, 1]]` has both row sums `−1` and eigenvalues `3` and `−1`, so `λ₁(A) = 3 ≠ Ā`.
The paper applies Fact 6 only to networks, which are nonnegative. Reading: when `Ā` is a
multiple eigenvalue "the" eigenvector `v₁(A)` depends on the basis, so the claim is that an
orthonormal eigenbasis with `v_{i₀} = 𝟏/√n` exists. `n ≥ 1` is needed for `λ₁(A)` to exist. -/
theorem fact_6 {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hsymm : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (Abar : ℝ) (hrow : ∀ i, ∑ j, A i j = Abar) :
    A *ᵥ (1 : Fin n → ℝ) = Abar • (1 : Fin n → ℝ) ∧
    Module.End.HasEigenvalue (Matrix.toLin' A) Abar ∧
    (∀ l : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) l → l ≤ Abar) ∧
    ∃ (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : Fin n → ℝ) (i₀ : Fin n),
      (∀ i, A *ᵥ ⇑(v i) = lam i • ⇑(v i)) ∧ lam i₀ = Abar ∧
      ⇑(v i₀) = (1 / Real.sqrt n) • (1 : Fin n → ℝ) ∧
      ∀ i, i ≠ i₀ → ∑ j, v i₀ j * v i j = 0 := by sorry

end NetServicePricing
