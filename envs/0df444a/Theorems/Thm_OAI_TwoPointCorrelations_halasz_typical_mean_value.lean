-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_mean_value
-- name    : OAI.TwoPointCorrelations.halasz_typical_mean_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:43.020381+00:00
-- url     : https://prove2.me/theorems/891f9aeb-5ddc-403f-bf18-b2bc3c369ce0
-- title:
--   Halász mean-value bound for the restriction of a multiplicative function to numbers divisible by a prime of each band
-- statement:
--   There are $C>0$ and $X_0$ such that for every natural $N\ge X_0$, every completely multiplicative $F$ on positive integers with $F(1)=1$ and $|F|\le1$, every index set $J$ with pairwise disjoint sets of primes $P_j\subseteq\{p\le N\}$ ($j\in J$), every $R$ with $\max(1,(\log N)^{16})\le R\le N/2$ and every prime of every $P_j$ at most $R$, and every $M\ge0$ with $\mathbb D(F,n^{it};N)^2\ge M$ for all $t\in[-(\log N)^8,(\log N)^8]$:
--
--   $$\Big|\sum_{n=1}^NG(n)\Big|\le CN\Big((M+1)e^{-M/2}+\frac{(1+\log R)\log\log N}{\log N}\Big),$$
--
--   where $G$ = `mrtTypicalCoefficient J P F` is $F(n)$ if every $P_j$ ($j\in J$) contains a prime divisor of $n$, and $0$ otherwise.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_typical_mean_value`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem halasz_typical_mean_value : ∃ C X₀ : ℝ, 0  <  C ∧
    ∀ N : ℕ, X₀  ≤  N → ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, P j  ⊆  primesUpTo N) → Set.PairwiseDisjoint (J : Set ι) P →
      ∀ R : ℝ, 1 ≤ R → Real.log (N:ℝ)^16 ≤ R → R ≤ (N:ℝ)/2 →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ R) → ∀ M : ℝ, 0 ≤ M →
      (∀ t ∈ Set.Icc (-(Real.log (N:ℝ)^8)) (Real.log (N:ℝ)^8),
        M ≤ squaredDistance F (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, mrtTypicalCoefficient J P F n‖  ≤  C*N*
        ((M+1)*Real.exp (-M/2)+(1+Real.log R)*Real.log (Real.log N)/Real.log N) := by
  sorry

end OAI.TwoPointCorrelations
