-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_quantitative_partial_tuple_bin
-- name    : OAI.TwoPointCorrelations.quantitative_partial_tuple_bin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:33.875976+00:00
-- url     : https://prove2.me/theorems/69068fc3-a6b8-4bdf-9eb7-6f943625844a
-- title:
--   Under Mertens' estimate and the Liouville short input, partial prime-tuple profiles have small mean
-- statement:
--   Assume `PrimeReciprocalInput` and `MRTLiouvilleShortInput`, and let $h>0$. Then there is $C>0$ such that for all sufficiently large $L$: for pairwise disjoint sets of primes $P_1,\dots,P_J$, a set $I$ of indices, naturals $q,X>0$ and $l\ne0$, an eligibility relation, $b\in\mathbb Z/l$ and reals $M$, $\tau\in(0,2)$, if for every choice $y$ of one prime from each $P_j$ with $j\notin I$: $q\prod_jy_j$ is a unit modulo $l$, $\lfloor X/(q\prod y_j)\rfloor\ge\exp(\frac12L^{1000})$, and every $z$ in the slice `primeTupleSlice P I` with $(\prod y_j\cdot z,q)$ eligible lies in $[\frac M{q\prod y_j},\tau\frac M{q\prod y_j}]\cap[e^{L^{199/200}},e^{2L}]$ and has no prime factor $\le\exp(L^{99/100})$, then
--
--   $$\Big|\frac1X\sum_{n=1}^{X}\texttt{tuplePartialProfile}(P,I,q,\mathrm{eligible},l,b,h,n)\Big|\le l\,C\,L^{-21/20}\cdot\frac1q\prod_{j\notin I}\sum_{p\in P_j}\frac1p.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.quantitative_partial_tuple_bin`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem quantitative_partial_tuple_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J : ℕ) (P : Fin J → Finset ℕ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j k, k ≠ j → Disjoint (P j) (P k)) →
      ∀ (I : Finset (Fin J)) (q X l : ℕ) [NeZero l],
      0 < q → 0 < X →
      ∀ (eligible : ℕ → ℕ → Prop) (b : ZMod l) (M : ℝ) (τ : ℝ),
      0 < τ → τ < 2 →
      (∀ y : (j : {j // j ∉ I}) → P j,
        IsUnit ((q * ∏ j, (y j).val : ℕ) : ZMod l)) →
      (∀ y : (j : {j // j ∉ I}) → P j,
        Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤
          ((X / (q * ∏ j, (y j).val) : ℕ) : ℝ)) →
      (∀ y : (j : {j // j ∉ I}) → P j, ∀ z ∈ primeTupleSlice P I,
        eligible ((∏ j, (y j).val) * z) q →
          M / (q * ∏ j, ((y j).val : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ τ * (M / (q * ∏ j, ((y j).val : ℝ))) ∧
          Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ Real.exp (2 * L) ∧
          avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ)‖ ≤
        ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) *
          ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j)) := by
  sorry

end OAI.TwoPointCorrelations
