-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_2_5
-- name    : HighPrecSAC1.Main.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:19.073216+00:00
-- url     : https://prove2.me/theorems/fa1e4f3e-7877-419f-834d-4b503a5f4b0b
-- title:
--   Lemma 2.5 — elementary floating-point operations
-- statement:
--   Let $p,b,q\ge1$ be logspace-computable, polynomially bounded integer functions of $n$. Polynomial-size L-uniform Boolean AC circuits of constant depth compute the following operations on nonnegative $(p,b)$-numbers:
--   1. $\operatorname{RoundDown}_q(A)$ and $\operatorname{RoundUp}_q(A)$.
--   2. $A+B$ and $[A-B]^+$ exactly, provided $b=O(\log n)$.
--   3. $AB$ exactly, provided $p=O(\log n)$.
--   Each case has fixed output word widths given by logspace-computable polynomially bounded functions. The two restrictions apply only to their respective cases. These are the elementary numerical primitives used in subsequent circuit constructions.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: polynomial size, L-uniformity and big-O bounds → explicit gate-and-wire size, self-delimiting binary descriptions, one finite transducer with c*(floor(log2(n+1))+1) work cells, and one bound constant before n; reason: the source leaves the equivalent machine and description conventions implicit; fixed source and output overhead changes no asymptotic size class
--   - encoding: gate-count depth and asymptotic circuit bounds → input and constant depth zero, maximum depth over output paths, and asymptotic bounds for n at least 3; reason: the layering uses depth-zero sources; finitely many small input lengths can be absorbed into constants; log log n is positive on the stated bound domain
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
--   - encoding: outputs of elementary operations without fixed width functions in the statement → existential logspace-computable polynomially bounded output widths; reason: the proof on printed page 36 explicitly bounds the output lengths; fixed widths make circuit outputs well-typed
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 2.5, printed p. 10 (PDF 11)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_2_5 :
    ∀ (p b q : ℕ → ℕ), Parameter p → Parameter b → Parameter q →
    (∃ po bo, Parameter po ∧ Parameter bo ∧
      Numerical (fun _ => 1) p b (fun _ => 2) po bo (fun _ => 1)
        (fun n A z => z 0 = roundDown (q n) (A 0) ∧ z 1 = roundUp (q n) (A 0))) ∧
    (LogBound b → ∃ po bo, Parameter po ∧ Parameter bo ∧
      Numerical (fun _ => 2) p b (fun _ => 2) po bo (fun _ => 1)
        (fun _ A z => z 0 = A 0 + A 1 ∧ z 1 = posSub (A 0) (A 1))) ∧
    (LogBound p → ∃ po bo, Parameter po ∧ Parameter bo ∧
      Numerical (fun _ => 2) p b (fun _ => 1) po bo (fun _ => 1)
        (fun _ A z => z 0 = A 0 * A 1)) := by sorry

end HighPrecSAC1.Main
