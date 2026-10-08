-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_tuple_column_array_cover
-- name    : OAI.TwoPointCorrelations.tuple_column_array_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:14:05.676079+00:00
-- url     : https://prove2.me/theorems/601abb04-b2d6-463c-baf2-b0f41c041045
-- title:
--   Low-rank surviving column words admit a budgeted column array code
-- statement:
--   Let $P_1,\dots,P_J$ be pairwise disjoint sets of primes, $w$ a column prime assignment with $R>0$ rows (`ColumnPrimeAssignment J R P`), directions and paddings, naturals $h,s>0$, $r$, a relation `supply`, $x\in\mathbb Z$, a set of perfect rows and a cut. Suppose: for each perfect row $i$, $\mathrm{padding}_i\cdot\mathrm{tuple}_i$ divides $x$ plus the displacement of the first $i$ steps; every step is in `supply`, has positive padding, a squarefree tuple with exactly $J$ prime factors; the word is nonbacktracking before and after the cut; tuple primes do not divide $h$ or any padding; every vertex of the word avoids the prohibited sites (`ProhibitedSite h s supply`); and for $L\ge1$: $R\le2L$, $s\ge L^{1/10}/2$, $r\le L^{1/50}$, the imperfect column count of the perfect rows other than the cut is at most $2L^{1/4}$, and every column pattern is of low rank (`ColumnLowRank … r`). Then there is a code in `BudgetColumnArrayCode J (2R) L` whose decoding (`decodeBudgetColumnArray`) returns, for every column $j$ and rows $i,l$, whether $w_j(i)=w_j(l)$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.tuple_column_array_cover`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem tuple_column_array_cover {J R : ℕ} (P : Fin J → Finset ℕ)
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    {h s r : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (hh : 0 < h) (hs : 0 < s)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hlit : ∀ i ∈ perfect, ((padding i : ℤ) * columnTuple w i) ∣
      x + wordDisplacement h ((columnTupleWord w forward padding).take i.val))
    (heligible : ∀ a ∈ columnTupleWord w forward padding, supply a.tuple a.padding)
    (hq : ∀ a ∈ columnTupleWord w forward padding, 0 < a.padding)
    (hsq : ∀ a ∈ columnTupleWord w forward padding, Squarefree a.tuple)
    (hcard : ∀ a ∈ columnTupleWord w forward padding, a.tuple.primeFactors.card = J)
    (hleft : ((columnTupleWord w forward padding).take cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hright : ((columnTupleWord w forward padding).drop cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (columnTupleWord w forward padding) p j →
      ¬p ∣ h ∧ ∀ a ∈ columnTupleWord w forward padding, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (columnTupleWord w forward padding) y →
      ¬ProhibitedSite h s supply y)
    (L : ℝ) (hL : 1 ≤ L) (hRL : (R : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount (perfect.erase cut) : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ j, ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r) :
    ∃ code : BudgetColumnArrayCode J (2 * R) L,
      ∀ j i l, decodeBudgetColumnArray (show R ≤ 2 * R by omega) code j i l =
        decide (w j i = w j l) := by
  sorry

end OAI.TwoPointCorrelations
