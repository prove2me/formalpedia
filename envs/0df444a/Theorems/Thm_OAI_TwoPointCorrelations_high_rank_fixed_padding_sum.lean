-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_high_rank_fixed_padding_sum
-- name    : OAI.TwoPointCorrelations.high_rank_fixed_padding_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:13.916989+00:00
-- url     : https://prove2.me/theorems/5c9b0f7f-4d65-4d5d-a391-0706e3f1ec4e
-- title:
--   The reciprocal weight of high-rank column assignments with fixed paddings
-- statement:
--   Let $J,R$ be naturals with $R>0$, $P_1,\dots,P_J$ finite sets of naturals, $F$ a finite set of column prime assignments (`ColumnPrimeAssignment J R P`: for each column $l$ and row $i$ an element of $P_l$), `forward` and `padding` row data, a column $j$, naturals $h,Q,D,B,H,r$ and $U\ge1$. Suppose the elements of $P_j$ are primes in $[H,B]$ with $H>0$ and $\sum_{p\in P_j}1/p>0$, $\sum_{p\in P_l}1/p\le U$ for every $l$, every padding is at most $Q$, for every $w\in F$ and row $i$ the product of the other columns' entries is at most $D$, no $w\in F$ has a low-rank $j$-th column pattern (not `ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r`), and for every $w\in F$ and perfect row $i$ the prime $w_j(i)$ divides $\mathrm{base}(w)$ plus the displacement of the first $i$ steps of the word (`wordDisplacement h`). Then
--
--   $$\sum_{w\in F}\prod_{l}\prod_{p\in\{w_l(i)\}_i}\frac1p\le\#\texttt{CrudeColumnPatternCode}(J,R)\cdot U^{RJ}\cdot\Big(\Big(\frac{1+\log_2(2RhQDB)}{H\sum_{p\in P_j}1/p}\Big)^r\Big)^{1/2},$$
--
--   where $\log_2$ is the natural-number binary logarithm (`Nat.log 2`) and the left side is `columnReciprocalWeight`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.high_rank_fixed_padding_sum`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem high_rank_fixed_padding_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P))
    (hR : 0 < R) (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (h Q D B H r : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hmass : ∀ l, primeHarmonicMass (P l) ≤ U) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ w ∈ F, ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ∀ w ∈ F,
      ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → ℤ)
    (hlit : ∀ w ∈ F, ∀ i ∈ perfect, ((w j i).val : ℤ) ∣ base w +
      wordDisplacement h ((columnTupleWord w forward padding).take i.val)) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤
      (Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J) *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r) := by
  sorry

end OAI.TwoPointCorrelations
