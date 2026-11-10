-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_6_3
-- name    : HighPrecSAC1.Main.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:28:50.797343+00:00
-- url     : https://prove2.me/theorems/5689a6e1-eeca-4143-b2df-046cf9adc9a0
-- title:
--   Lemma 6.3 — initialization with nonnegative residuals
-- statement:
--   For the scaled and truncated system of Lemma 6.2, define $y_0=x_0$ and $y_i=(1-4^i\eta)b_i$ for $1\le i\le K$. Then
--   $$0\le y\le\Phi(y)\le X,\qquad X-y\le\alpha_0X,\qquad\alpha_0=2\cdot4^K\eta,$$
--   so $r=\Phi(y)-y\ge0$. With $J=D\Phi(y)$,
--   $$G_\eta=(I-(1-\eta)J)^{-1}=\sum_{j=0}^{K}(1-\eta)^jJ^j.$$
--   Let $R$ be any lower approximation with the precision guaranteed by Lemma 3.2 for the geometric-doubling circuit. Then
--   $$(1-\eta)G_\eta\le R\le G_\eta,\qquad R\ge0,\qquad
--   E=I-(I-J)R\ge0,\qquad EX\le\beta_0X,$$
--   where $\beta_0=(K+1)\eta H$ and $H=2^{K+1}-1$. Every entry of $y,r,R,E$ is a $(n^{O(1)},O(\log n))$-number, with logspace-computable common widths. This is the full initialization guarantee, including both the inverse identity and the representation assertion.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
--   - generalization: the preliminary approximations computed by Theorem 3.1 → every family of normalized words satisfying that theorem's prescribed precision, exponent bound and relative-error guarantee; reason: the rescaling and truncation construction is concrete and the source's choice satisfies these conditions
--   - generalization: R is the lower approximation from the geometric-doubling circuit and Lemma 3.2 → every R with (1-eta)*G_eta at most R at most G_eta and precision at most tau+c*(floor(log2(K+2))+1)+9 for one family-wide constant c; reason: Lemma 3.2 gives this precision for arithmetic depth O(log(K+2)); its particular R is included without assuming the inverse-residual conclusion
--   - generalization: a logspace-computable polynomial upper bound N >= 2 on the gates and wires of the copied circuit → N >= 2 with (K+1)*gates+K*sum(arity) <= N; reason: every count of the copied circuit's gates and wires is at least this (source-copy and output wires are left out), so every N the source allows is admitted; the proof uses N only to bound the monomial occurrences of a coordinate
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 6.3, printed p. 29 (PDF 30)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_6_3 :
    ∀ D : PreparationFamily, D.valid → ∀ c : ℕ,
    ∃ p b : ℕ → ℕ, Parameter p ∧ Parameter b ∧ LogBound b ∧
    ∀ n, 1 ≤ n → ∀ x, ∀ R : GMat (D.K n) (D.circuits n).gates,
      InitialR (D.system n x) (D.bhat n x) c R →
      let S := D.system n x
      let T := initialState S (D.bhat n x) R
      let J := S.jac T.y
      let G := geometricInverse S T.y
      0 ≤ T.y ∧ T.y ≤ S.global T.y ∧ S.global T.y ≤ S.exact ∧
      S.exact - T.y ≤ alpha0 (D.K n) • S.exact ∧ 0 ≤ T.r ∧
      (1 - (1-eta (D.K n)) • J)⁻¹ = G ∧
      EntryLE ((1-eta (D.K n)) • G) R ∧ EntryLE R G ∧ EntryLE 0 R ∧ EntryLE 0 T.E ∧
      T.E.mulVec S.exact ≤ beta0 (D.K n) • S.exact ∧
      (∀ z ∈ stateEntries T, IsFloat (p n) (b n) z) := by sorry

end HighPrecSAC1.Main
