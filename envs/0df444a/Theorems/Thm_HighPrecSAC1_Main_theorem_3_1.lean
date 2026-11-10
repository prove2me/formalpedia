-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_theorem_3_1
-- name    : HighPrecSAC1.Main.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:28:19.468966+00:00
-- url     : https://prove2.me/theorems/d37ea695-f1fb-48bd-bd91-78ef4f730719
-- title:
--   Theorem 3.1 (= 1.4) — multiplicative approximation in depth O(K+t)
-- statement:
--   Let $K,t\ge1$ be arbitrary logspace-computable polynomially bounded integer functions, and let $(G_n)$ be any polynomial-size L-uniform family of positive semi-unbounded arithmetic circuits of depth at most $K(n)$ computing $F_n:\{0,1\}^n\to\mathbb N$. There exists a polynomial-size L-uniform Boolean AC family of depth
--   $$O(K(n)+t(n))$$
--   which, on every Boolean input $x$, outputs a nonnegative $(t(n)+2,O(K(n)+\log n))$-number $\widetilde F_n(x)$ such that
--   $$(1-2^{-t(n)})F_n(x)\le\widetilde F_n(x)\le F_n(x).$$
--   The same family is L-uniform AC¹ when $K,t=O(\log n)$. The circuit family, width function, transducer, polynomial size bound and all asymptotic constants are chosen before $n$ and $x$. This is Theorem 1.4 restated as Theorem 3.1, including its final AC¹ clause.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: polynomial size, L-uniformity and big-O bounds → explicit gate-and-wire size, self-delimiting binary descriptions, one finite transducer with c*(floor(log2(n+1))+1) work cells, and one bound constant before n; reason: the source leaves the equivalent machine and description conventions implicit; fixed source and output overhead changes no asymptotic size class
--   - encoding: gate-count depth and asymptotic circuit bounds → input and constant depth zero, maximum depth over output paths, and asymptotic bounds for n at least 3; reason: the layering uses depth-zero sources; finitely many small input lengths can be absorbed into constants; log log n is positive on the stated bound domain
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Theorem 3.1, printed p. 11 (PDF 12) Also Theorem 1.4, printed p. 3 (PDF 4).

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem theorem_3_1 :
    ∀ (K t : ℕ → ℕ), Parameter K → Parameter t →
    ∀ (G : ∀ n, PositiveCircuit n) (F : ∀ n, (Fin n → Bool) → ℕ),
    AUniform G → APoly G → (∀ n, 1 ≤ n → (G n).depth ≤ K n) → AComputes G F →
    Approximates F K t 2 (fun n => (K n : ℝ)+t n) (LogBound K ∧ LogBound t) := by sorry

end HighPrecSAC1.Main
