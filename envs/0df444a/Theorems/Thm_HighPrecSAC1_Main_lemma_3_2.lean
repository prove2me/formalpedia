-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_3_2
-- name    : HighPrecSAC1.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:00.74136+00:00
-- url     : https://prove2.me/theorems/e8a289de-8cfe-472c-941e-e58943e65a02
-- title:
--   Lemma 3.2 — shallow positive arithmetic evaluation
-- statement:
--   Let $p,b,q,h\ge1$ be logspace-computable, polynomially bounded integer functions. Let $(H_n)_{n\ge4}$ be a polynomial-size L-uniform family of positive semi-unbounded arithmetic circuits of depth at most $h(n)$, with arbitrary nonnegative $(p,b)$-number inputs and arithmetic constants. There is a polynomial-size L-uniform Boolean AC family of depth
--   $$O\left(h\left(1+\frac{\min\{q+h,\log n\}}{\log\log n}\right)\right)$$
--   which for every designated output value $z$ produces $(q+h+9,O(b+h+\log\log n))$-numbers $L,U$ satisfying
--   $$(1-2^{-q})z\le L\le z\le U\le(1+2^{-q})z.$$
--   All outputs are produced in the order of the designated arithmetic outputs, with a lower and upper word for each. The transducer is fixed after the parameter functions; no stronger uniformity in extra parameters is asserted.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: polynomial size, L-uniformity and big-O bounds → explicit gate-and-wire size, self-delimiting binary descriptions, one finite transducer with c*(floor(log2(n+1))+1) work cells, and one bound constant before n; reason: the source leaves the equivalent machine and description conventions implicit; fixed source and output overhead changes no asymptotic size class
--   - encoding: gate-count depth and asymptotic circuit bounds → input and constant depth zero, maximum depth over output paths, and asymptotic bounds for n at least 3; reason: the layering uses depth-zero sources; finitely many small input lengths can be absorbed into constants; log log n is positive on the stated bound domain
--   - encoding: normalized odd significand and signed exponent of at most p and b bits with a zero flag → fixed layout: zero flag, p little-endian significand bits, sign bit, then b-1 little-endian magnitude bits; invalid input words are unrestricted; reason: padding changes no represented number and fixes the meaning of circuit input and output bits
--   - encoding: positive integer functions and asymptotic polynomial bounds → natural-valued functions positive for n at least 1, with f(n) at most c*(n+1)^d; reason: values at zero are unused and this is equivalent to the stated asymptotic polynomial bound
--   - encoding: arithmetic inputs and one or more designated outputs → an explicit logspace polynomial input-count function m (possibly zero) and positive output-count function o; lower and upper outputs are interleaved; reason: counts can be read from the explicit uniform circuit description; this includes constant-only circuits and retains every output
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 3.2, printed p. 12 (PDF 13)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_3_2 :
    ∀ (m o p b q h : ℕ → ℕ), Logspace m → PolyBound m → Parameter o →
    Parameter p → Parameter b → Parameter q → Parameter h →
    ∀ A : ∀ n, ACircuit (NumericalAtom (m n)) (o n),
    UniformWords (fun n => codeNat (m n) ++ (A n).description (NumericalAtom.code (p n) (b n))) 4 →
    PolyBound (fun n => (A n).size) →
    (∀ n, 4 ≤ n → (A n).depth ≤ h n ∧ NumericalConstantsValid (p n) (b n) (A n)) →
    ∃ bo, Parameter bo ∧ Bound (fun n => bo n) (fun n => (b n : ℝ)+h n+lg (lg n)) 4 ∧
      Numerical m p b (fun n => 2*o n) (fun n => q n+h n+9) bo
        (fun n => (h n : ℝ)*(1 + min ((q n+h n : ℕ):ℝ) (lg n)/lg (lg n)))
        (fun n x z => ∀ j : Fin (o n),
          let L := z ⟨2*j.val, by omega⟩
          let U := z ⟨2*j.val+1, by omega⟩
          let v := (A n).eval (NumericalAtom.value x) j
          (1-err (q n))*v ≤ L ∧ L ≤ v ∧ v ≤ U ∧ U ≤ (1+err (q n))*v) 4 := by sorry

end HighPrecSAC1.Main
