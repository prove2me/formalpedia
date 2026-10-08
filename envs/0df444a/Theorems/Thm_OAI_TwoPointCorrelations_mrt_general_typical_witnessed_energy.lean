-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_general_typical_witnessed_energy
-- name    : OAI.TwoPointCorrelations.mrt_general_typical_witnessed_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:36.29633+00:00
-- url     : https://prove2.me/theorems/5d02aa9f-ca5b-41fa-9014-ed1436b46f30
-- title:
--   Mean square of the typical dyadic polynomial on a set covered by large values of earlier prime polynomials
-- statement:
--   Let $J$, the pairwise disjoint sets of primes $P_i$, $j\in J$, the bins $K$, bin map, lower endpoints $\ell\ge1$, $N\ge1$, $\delta\in[1,2]$, and $F$ be as in the companion small-prime statement (with $\ell(\mathrm{bin}(p))\le p\le\delta\ell(\mathrm{bin}(p))$ on $P_j$, $F$ multiplicative and bounded by $1$). Let $B$ be a finite set with, for $b\in B$, sets of primes $P'_b\subseteq[Y_b,2Y_b]$ with $Y_b>1$ and thresholds $V_b>0$; let $T>0$, $E\subseteq(-T,T]$ measurable, and $A:K\to\mathbb R$ with $\big|\sum_{p\in P_j,\mathrm{bin}(p)=k}\frac{F(p)}pp^{-it}\big|\le A(k)$ on $E$, and suppose every $t\in E$ has some $b\in B$ with $\big|\sum_{p\in P'_b}\frac{F(p)}pp^{-it}\big|\ge V_b$. Then, with $D_N$ the dyadic polynomial of $G$ = `mrtTypicalCoefficient J P F` and $a_{b,k}=\lceil\log\ell(k)/\log\lceil Y_b\rceil\rceil$ (`mrtAmplificationOrder ⌈Y b⌉ (ℓ k)`),
--
--   $$\int_E|D_N|^2\le2816e\Big(\frac TN+1\Big)\Big(\sum_{P_j}\tfrac1{p^2}+\big(\sum_{P_j}\tfrac1{p^2}\big)^2+\delta-1\Big)+2\sum_{b\in B}\#K\sum_{k\in K}A(k)^2\,\frac{16e^{10}\big(\frac TN+2^{a_{b,k}+1}\lceil Y_b\rceil\big)(a_{b,k}!)^2}{V_b^{2a_{b,k}}}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_general_typical_witnessed_energy`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_general_typical_witnessed_energy {ι κ β : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k)
    (F : ℕ → ℂ)
    (hF : Multiplicative F)
    (hFb : OneBounded F)
    (B : Finset β) (Pprev : β → Finset ℕ) (Y : β → ℝ)
    (hY : ∀ b ∈ B, 1 < Y b)
    (hprev : ∀ b ∈ B, ∀ p ∈ Pprev b, p.Prime)
    (hprevbin : ∀ b ∈ B, ∀ p ∈ Pprev b, Y b ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y b)
    (V : β → ℝ) (hV : ∀ b ∈ B, 0 < V b)
    {T : ℝ} (hT : 0 < T) {E : Set ℝ} (hE : MeasurableSet E)
    (hET : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k)
    (hcover : ∀ t ∈ E, ∃ b ∈ B, V b ≤
      ‖mrtExponentialPolynomial (Pprev b) (fun p => F p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      2816 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      2 * ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
        ((16 * Real.exp 10 *
          (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y b⌉₊ (lower k) + 1) * ⌈Y b⌉₊) *
            ((mrtAmplificationOrder ⌈Y b⌉₊ (lower k)).factorial : ℝ) ^ 2) /
          (V b) ^ (2 * mrtAmplificationOrder ⌈Y b⌉₊ (lower k))) := by
  sorry

end OAI.TwoPointCorrelations
