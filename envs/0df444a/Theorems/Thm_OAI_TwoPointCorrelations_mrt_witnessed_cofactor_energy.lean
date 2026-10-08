-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_witnessed_cofactor_energy
-- name    : OAI.TwoPointCorrelations.mrt_witnessed_cofactor_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:31.178541+00:00
-- url     : https://prove2.me/theorems/3ff6b599-dfb7-4a2c-a1b2-f1d164da1eb2
-- title:
--   Amplification bound for binned products of small polynomials and cofactor polynomials on a covered set
-- statement:
--   Let $K$ be a finite set of bins with continuous $Q_k:\mathbb R\to\mathbb C$, bounds $A_k$ and lower endpoints $\ell_k\ge1$; $P$ a finite set; $F$ bounded by $1$ on positive integers; $N\ge1$; $B$ a finite set with, for $b\in B$, sets of primes $P'_b\subseteq[Y_b,2Y_b]$, $Y_b>1$, coefficients $a_b$ with $|a_b|\le1$ on $P'_b$ and thresholds $V_b>0$; $T>0$ and $S\subseteq(-T,T]$ measurable with $|Q_k|\le A_k$ on $S$ and every $t\in S$ having some $b$ with $\big|\sum_{p\in P'_b}\frac{a_b(p)}pp^{-it}\big|\ge V_b$. Then, with $m_{b,k}=\lceil\log\ell_k/\log\lceil Y_b\rceil\rceil$,
--
--   $$\int_S\Big|\sum_{k\in K}Q_k(t)\,\mathcal C_k(t)\Big|^2dt\le\sum_{b\in B}\#K\sum_{k\in K}A_k^2\,\frac{16e^{10}\big(\frac TN+2^{m_{b,k}+1}\lceil Y_b\rceil\big)(m_{b,k}!)^2}{V_b^{2m_{b,k}}},$$
--
--   where $\mathcal C_k$ = `mrtCofactorPolynomial P F N ℓ_k`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_witnessed_cofactor_energy`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_witnessed_cofactor_energy {κ β : Type*}
    (K : Finset κ) (Q : κ → ℝ → ℂ) (A lower : κ → ℝ)
    (P : Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) (hlower : ∀ k ∈ K, 1 ≤ lower k)
    (B : Finset β) (Pprev : β → Finset ℕ) (Y : β → ℝ)
    (hY : ∀ b ∈ B, 1 < Y b)
    (hPprev : ∀ b ∈ B, ∀ p ∈ Pprev b, p.Prime)
    (hprevbin : ∀ b ∈ B, ∀ p ∈ Pprev b, Y b ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y b)
    (a : β → ℕ → ℂ) (ha : ∀ b ∈ B, ∀ p ∈ Pprev b, ‖a b p‖ ≤ 1)
    (V : β → ℝ) (hV : ∀ b ∈ B, 0 < V b)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : MeasurableSet S)
    (hST : S ⊆ Set.Ioc (-T) T) (hQ : ∀ k ∈ K, Continuous (Q k))
    (hsmall : ∀ k ∈ K, ∀ t ∈ S, ‖Q k t‖ ≤ A k)
    (hcover : ∀ t ∈ S, ∃ b ∈ B, V b ≤
      ‖mrtExponentialPolynomial (Pprev b) (fun p => a b p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in S, ‖∑ k ∈ K, Q k t * mrtCofactorPolynomial P F N (lower k) t‖ ^ 2) ≤
      ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
        ((16 * Real.exp 10 *
          (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y b⌉₊ (lower k) + 1) * ⌈Y b⌉₊) *
            ((mrtAmplificationOrder ⌈Y b⌉₊ (lower k)).factorial : ℝ) ^ 2) /
          (V b) ^ (2 * mrtAmplificationOrder ⌈Y b⌉₊ (lower k))) := by
  sorry

end OAI.TwoPointCorrelations
