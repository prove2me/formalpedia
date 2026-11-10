-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_2_8
-- name    : HighPrecSAC1.Main.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:20.122119+00:00
-- url     : https://prove2.me/theorems/502eb47b-8656-46cf-ac8a-e208c7e20da1
-- title:
--   Lemma 2.8 — directed approximate summation
-- statement:
--   Let $m,p,b,q\ge1$ be logspace-computable, polynomially bounded integer functions. There is a polynomial-size L-uniform Boolean AC family of depth
--   $$O\left(1+\frac{\min\{q,\log n\}}{\log\log n}\right)$$
--   which, on nonnegative $(p,b)$-numbers $A_1,\ldots,A_m$, outputs $(q+6,b+O(\log\log n))$-numbers $L,U$ with
--   $$(1-2^{-q})S\le L\le S\le U\le(1+2^{-q})S,\qquad S=\sum_i A_i.$$
--   No restriction $b=O(\log n)$ is assumed. This is a directed relative approximation of a positive sum.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: polynomial size, L-uniformity and big-O bounds → explicit gate-and-wire size, self-delimiting binary descriptions, one finite transducer with c*(floor(log2(n+1))+1) work cells, and one bound constant before n; reason: the source leaves the equivalent machine and description conventions implicit; fixed source and output overhead changes no asymptotic size class
--   - encoding: gate-count depth and asymptotic circuit bounds → input and constant depth zero, maximum depth over output paths, and asymptotic bounds for n at least 3; reason: the layering uses depth-zero sources; finitely many small input lengths can be absorbed into constants; log log n is positive on the stated bound domain
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 2.8, printed p. 11 (PDF 12)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_2_8 :
    ∀ (m p b q : ℕ → ℕ), Parameter m → Parameter p → Parameter b → Parameter q →
    ∃ bo, Parameter bo ∧ Bound (fun n => (bo n : ℝ) - b n) (fun n => lg (lg n)) ∧
      Numerical m p b (fun _ => 2) (fun n => q n+6) bo
        (fun n => 1 + min (q n : ℝ) (lg n) / lg (lg n))
        (fun n A z => (1-err (q n))*(∑ j, A j) ≤ z 0 ∧
          z 0 ≤ ∑ j, A j ∧ (∑ j, A j) ≤ z 1 ∧ z 1 ≤ (1+err (q n))*(∑ j, A j)) := by sorry

end HighPrecSAC1.Main
