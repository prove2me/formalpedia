-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_6_2
-- name    : HighPrecSAC1.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:28:58.082207+00:00
-- url     : https://prove2.me/theorems/0ddb8e35-9ad4-4a41-aa23-991adfedc55f
-- title:
--   Lemma 6.2 — rescaling and coefficient truncation
-- statement:
--   Use the copy-per-layer arithmetic circuit, preliminary words $\bar b$, and concrete rescaling, zero-monomial deletion and coefficient truncation of Section 6.1. Put $\tau=6K+20$, $\eta=2^{-\tau}$, $\rho=\eta/4$, $P=K+\lceil\log_2 N\rceil+\max\{t,\tau\}+10$, and $\varepsilon=8N(2^K-1)2^{-P}$. The scaled original values $Z$, truncated exact values $\widehat X$, and the prescribed approximation $\widehat b$ satisfy
--   $$\varepsilon<2^{-\max\{t,\tau\}-7},\qquad
--   (1-\varepsilon)Z\le\widehat X\le Z,\qquad
--   (1-2^{-\tau})\widehat X\le\widehat b\le\widehat X.$$
--   Each nonzero coordinate of $Z$ lies in $[1/2,2]$. Every nonzero monomial-occurrence coefficient of $\widehat\Phi$ is a $(1,O(\log n))$-number, is a multiple of $2^{-P}$, and is at most $8$. Each entry of $\widehat b$ is a $(2\tau+6,O(\log n))$-number. The representation widths are chosen uniformly before the input length and Boolean assignment.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
--   - generalization: the preliminary approximations computed by Theorem 3.1 → every family of normalized words satisfying that theorem's prescribed precision, exponent bound and relative-error guarantee; reason: the rescaling and truncation construction is concrete and the source's choice satisfies these conditions
--   - generalization: a logspace-computable polynomial upper bound N >= 2 on the gates and wires of the copied circuit → N >= 2 with (K+1)*gates+K*sum(arity) <= N; reason: every count of the copied circuit's gates and wires is at least this (source-copy and output wires are left out), so every N the source allows is admitted; the proof uses N only to bound the monomial occurrences of a coordinate
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 6.2, printed p. 28 (PDF 29)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_6_2 :
    ∀ D : PreparationFamily, D.valid →
    ∃ b : ℕ → ℕ, Parameter b ∧ LogBound b ∧
    ∀ n, 1 ≤ n → ∀ x,
      let K := D.K n
      let S := D.system n x
      let Z := scaledExact (D.circuits n) K x (D.bar n x)
      let eps := truncationError K (D.t n) (D.N n)
      eps < err (max (D.t n) (tau K)+7) ∧
      (1-eps) • Z ≤ S.exact ∧ S.exact ≤ Z ∧
      (1-eta K) • S.exact ≤ D.bhat n x ∧ D.bhat n x ≤ S.exact ∧
      (∀ v, Z v ≠ 0 → 1/2 ≤ Z v ∧ Z v ≤ 2) ∧
      (∀ i j a, a ∈ S.layer i j → a.coeff ≠ 0 →
        IsFloat 1 (b n) a.coeff ∧ a.coeff ≤ 8 ∧
        ∃ z : ℕ, a.coeff = (z:ℝ)*err (truncationBits K (D.t n) (D.N n))) ∧
      (∀ v, IsFloat (2*tau K+6) (b n) (D.bhat n x v)) := by sorry

end HighPrecSAC1.Main
