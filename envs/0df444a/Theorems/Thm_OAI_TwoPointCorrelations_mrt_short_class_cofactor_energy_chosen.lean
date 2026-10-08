-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_short_class_cofactor_energy_chosen
-- name    : OAI.TwoPointCorrelations.mrt_short_class_cofactor_energy_chosen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:19.771756+00:00
-- url     : https://prove2.me/theorems/594f37ac-47f2-4dde-ae0d-0d7680bc2843
-- title:
--   Amplification bound for a cofactor polynomial on a set where a short prime polynomial is large
-- statement:
--   Let $P,Q$ be finite sets of naturals with $P$ a set of primes in $[Y,2Y]$ for a natural $Y>1$, $N\ge1$, $a:\mathbb N\to\mathbb C$ with $|a|\le1$ on $P$, $F$ bounded by $1$ on positive integers, $u\ge1$, $T,V>0$, and $E\subseteq(-T,T]$ such that $\big|\sum_{p\in P}\frac{a(p)}pp^{-it}\big|\ge V$ for every $t\in E$. Then, with $m=\lceil\log u/\log Y\rceil$ (`mrtAmplificationOrder Y u`),
--
--   $$\int_E\big|\mathcal C(t)\big|^2dt\le\frac{16e^{10}\big(\frac TN+2^{m+1}Y\big)(m!)^2}{V^{2m}},$$
--
--   where $\mathcal C(t)$ = `mrtCofactorPolynomial Q F N u t` $=\sum_{1\le n\le4N,\ N<un\le2N}\frac{F(n)n^{-1-it}}{\#\{p\in Q:p\mid n\}+1}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_short_class_cofactor_energy_chosen`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_short_class_cofactor_energy_chosen (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 1 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 *
        (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder Y u + 1) * Y) *
          ((mrtAmplificationOrder Y u).factorial : ℝ) ^ 2) /
        V ^ (2 * mrtAmplificationOrder Y u) := by
  sorry

end OAI.TwoPointCorrelations
