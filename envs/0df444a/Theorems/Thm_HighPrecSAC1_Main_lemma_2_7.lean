-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_2_7
-- name    : HighPrecSAC1.Main.lemma_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:28:27.059435+00:00
-- url     : https://prove2.me/theorems/6ef6077d-0db8-4a66-b3bf-cdef5e5fed42
-- title:
--   Lemma 2.7 — exact multiplication and iterated sum
-- statement:
--   Let $m,p,b\ge1$ be logspace-computable, polynomially bounded integer functions. Polynomial-size L-uniform Boolean AC circuits of depth $O(\log n/\log\log n)$ perform both operations:
--   1. The exact product of two nonnegative $(p,b)$-numbers, represented as a $(2p,b+2)$-number.
--   2. If $b=O(\log n)$, the exact sum $S=\sum_{i=1}^m A_i$ of $m$ nonnegative $(p,b)$-numbers, represented with
--   $$p'=p+2^b+\lceil\log_2 m\rceil+2,\qquad b'=b+O(\log\log n).$$
--   The exponential $2^b$ is the printed formula. The size and uniformity conditions accompany both clauses. These bounds support the exact matrix arithmetic of the refinement rounds.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: polynomial size, L-uniformity and big-O bounds → explicit gate-and-wire size, self-delimiting binary descriptions, one finite transducer with c*(floor(log2(n+1))+1) work cells, and one bound constant before n; reason: the source leaves the equivalent machine and description conventions implicit; fixed source and output overhead changes no asymptotic size class
--   - encoding: gate-count depth and asymptotic circuit bounds → input and constant depth zero, maximum depth over output paths, and asymptotic bounds for n at least 3; reason: the layering uses depth-zero sources; finitely many small input lengths can be absorbed into constants; log log n is positive on the stated bound domain
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 2.7, printed p. 11 (PDF 12)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_2_7 :
    ∀ (m p b : ℕ → ℕ), Parameter m → Parameter p → Parameter b →
    Numerical (fun _ => 2) p b (fun _ => 1) (fun n => 2*p n) (fun n => b n+2)
      (fun n => lg n / lg (lg n)) (fun _ A z => z 0 = A 0*A 1) ∧
    (LogBound b → ∃ bo, Parameter bo ∧
      Bound (fun n => (bo n : ℝ) - b n) (fun n => lg (lg n)) ∧
      Numerical m p b (fun _ => 1) (fun n => p n + 2^(b n) + ceilLog (m n) + 2) bo
        (fun n => lg n / lg (lg n)) (fun _ A z => z 0 = ∑ j, A j)) := by sorry

end HighPrecSAC1.Main
