-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_2_6
-- name    : HighPrecSAC1.Main.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:28:39.258272+00:00
-- url     : https://prove2.me/theorems/cc6df879-add4-4331-b30f-6232f767e1c1
-- title:
--   Lemma 2.6 — rounded addition and subtraction
-- statement:
--   Let $p,b,q\ge1$ be logspace-computable, polynomially bounded functions. On any two nonnegative $(p,b)$-numbers $A,B$, polynomial-size L-uniform constant-depth Boolean AC circuits compute all four values
--   $$\operatorname{RoundDown}_q(A+B),\quad\operatorname{RoundUp}_q(A+B),\quad
--   \operatorname{RoundDown}_q([A-B]^+),\quad\operatorname{RoundUp}_q([A-B]^+).$$
--   Every output is a $(q,b+O(\log n))$-number. There is no logarithmic restriction on the input exponent width $b$. This allows rounded subtraction even when exact subtraction has a very long significand.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: polynomial size, L-uniformity and big-O bounds → explicit gate-and-wire size, self-delimiting binary descriptions, one finite transducer with c*(floor(log2(n+1))+1) work cells, and one bound constant before n; reason: the source leaves the equivalent machine and description conventions implicit; fixed source and output overhead changes no asymptotic size class
--   - encoding: gate-count depth and asymptotic circuit bounds → input and constant depth zero, maximum depth over output paths, and asymptotic bounds for n at least 3; reason: the layering uses depth-zero sources; finitely many small input lengths can be absorbed into constants; log log n is positive on the stated bound domain
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 2.6, printed p. 11 (PDF 12)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_2_6 :
    ∀ (p b q : ℕ → ℕ), Parameter p → Parameter b → Parameter q →
    ∃ bo, Parameter bo ∧ Bound (fun n => (bo n : ℝ) - b n) (fun n => lg n) ∧
      Numerical (fun _ => 2) p b (fun _ => 4) q bo (fun _ => 1)
        (fun n A z => z 0 = roundDown (q n) (A 0 + A 1) ∧
          z 1 = roundUp (q n) (A 0 + A 1) ∧
          z 2 = roundDown (q n) (posSub (A 0) (A 1)) ∧
          z 3 = roundUp (q n) (posSub (A 0) (A 1))) := by sorry

end HighPrecSAC1.Main
