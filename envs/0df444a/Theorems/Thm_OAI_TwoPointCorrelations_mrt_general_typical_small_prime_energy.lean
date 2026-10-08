-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_general_typical_small_prime_energy
-- name    : OAI.TwoPointCorrelations.mrt_general_typical_small_prime_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:29.064772+00:00
-- url     : https://prove2.me/theorems/b1b47c06-71c6-4e0a-91f5-43901734a964
-- title:
--   Mean square of the typical dyadic polynomial on a set where the prime polynomials of one band are small
-- statement:
--   Let $J$ be a finite index set with pairwise disjoint sets of primes $P_i$, $j\in J$, $K$ a finite set of bins with a bin map sending $P_j$ into $K$, lower endpoints $\ell\ge1$ on $K$ with $N/\ell(k)\ge2$, $N\ge1$, $\delta\in[1,2]$ with $\ell(\mathrm{bin}(p))\le p\le\delta\ell(\mathrm{bin}(p))$ for $p\in P_j$; let $F$ be multiplicative and bounded by $1$ on positive integers, $T>0$, $E\subseteq(-T,T]$ and $A:K\to\mathbb R$ with $\big|\sum_{p\in P_j,\ \mathrm{bin}(p)=k}\frac{F(p)}pp^{-it}\big|\le A(k)$ for all $k\in K$, $t\in E$. Then, with $G$ = `mrtTypicalCoefficient J P F` and $D_N(t)=\sum_{N<n\le2N}\frac{G(n)}nn^{-it}$,
--
--   $$\int_E|D_N(t)|^2dt\le2816e\Big(\frac TN+1\Big)\Big(\sum_{p\in P_j}\frac1{p^2}+\Big(\sum_{p\in P_j}\frac1{p^2}\Big)^2+(\delta-1)\Big)+64e\,\#K\sum_{k\in K}A(k)^2\Big(\frac{T\ell(k)}N+1\Big).$$
--
--   (The integral is the Lebesgue integral of a nonnegative function over $E$, with Lean's convention that a non-integrable integrand integrates to $0$.)
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_general_typical_small_prime_energy`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_general_typical_small_prime_energy {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k) (hupper : ∀ k ∈ K, 2 ≤ (N : ℝ) / lower k)
    (F : ℕ → ℂ)
    (hF : Multiplicative F)
    (hFb : OneBounded F) {T : ℝ} (hT : 0 < T)
    (E : Set ℝ) (hE : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      2816 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      64 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
  sorry

end OAI.TwoPointCorrelations
