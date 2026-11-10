-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_6_7
-- name    : HighPrecSAC1.Main.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:01.338809+00:00
-- url     : https://prove2.me/theorems/687ae992-e4e9-49ab-a1b4-d7d2331fa23e
-- title:
--   Lemma 6.7 — polynomial precision during exact refinement
-- statement:
--   Fix a real constant $a>0$ and suppose $t(n)\le n^a$. For the scaled construction and every permitted initial tuple of Lemma 6.3, perform the $q$ rounds specified in (6.5). There exist positive logspace-computable integer functions $p,b$ such that
--   $$p(n)=n^{O(1)},\qquad b(n)=O(\log n),$$
--   and, for every input length, every Boolean assignment and every such initial tuple, all state entries and every vector or matrix materialized in (6.4) have $(p(n),b(n))$ representations throughout the rounds. This includes the initial and final states and the intermediates $s,Q(s),Er,DQ(s),DQ(s)R,B,RB$. No rounding is inserted into the updates.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
--   - generalization: the preliminary approximations computed by Theorem 3.1 → every family of normalized words satisfying that theorem's prescribed precision, exponent bound and relative-error guarantee; reason: the rescaling and truncation construction is concrete and the source's choice satisfies these conditions
--   - generalization: R is the lower approximation from the geometric-doubling circuit and Lemma 3.2 → every R with (1-eta)*G_eta at most R at most G_eta and precision at most tau+c*(floor(log2(K+2))+1)+9 for one family-wide constant c; reason: Lemma 3.2 gives this precision for arithmetic depth O(log(K+2)); its particular R is included without assuming the inverse-residual conclusion
--   - generalization: a logspace-computable polynomial upper bound N >= 2 on the gates and wires of the copied circuit → N >= 2 with (K+1)*gates+K*sum(arity) <= N; reason: every count of the copied circuit's gates and wires is at least this (source-copy and output wires are left out), so every N the source allows is admitted; the proof uses N only to bound the monomial occurrences of a coordinate
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 6.7, printed p. 32 (PDF 33)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_6_7 :
    ∀ (a : ℝ), 0 < a → ∀ D : PreparationFamily, D.valid →
    (∀ n, 1 ≤ n → (D.t n : ℝ) ≤ (n:ℝ)^a) → ∀ c : ℕ,
    ∃ p b : ℕ → ℕ, Parameter p ∧ Parameter b ∧ LogBound b ∧
    ∀ n, 1 ≤ n → ∀ x, ∀ R : GMat (D.K n) (D.circuits n).gates,
      InitialR (D.system n x) (D.bhat n x) c R →
      let S := D.system n x
      let T := initialState S (D.bhat n x) R
      let q := roundCount (D.K n) (D.t n)
      (∀ j, j ≤ q → ∀ z ∈ stateEntries (rounds S T j), IsFloat (p n) (b n) z) ∧
      (∀ j, j < q → ∀ z ∈ stepEntries S (rounds S T j), IsFloat (p n) (b n) z) := by sorry

end HighPrecSAC1.Main
