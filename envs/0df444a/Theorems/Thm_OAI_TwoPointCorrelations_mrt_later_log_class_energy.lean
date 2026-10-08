-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_later_log_class_energy
-- name    : OAI.TwoPointCorrelations.mrt_later_log_class_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:40.154988+00:00
-- url     : https://prove2.me/theorems/ac32eb6a-a705-41e2-aeaf-c965e07fd0e4
-- title:
--   Mean square of the typical dyadic polynomial on the later logarithmic class of a Matomäki–Radziwiłł band
-- statement:
--   Let $J$ be a finite index set with pairwise disjoint sets of primes $V_\nu$, $\nu\in J$ fixed, $S_0$ a finite set of primes, and reals $P>0$, $Q$, $\eta\in(0,1/6]$ with $\log P\ge2$, $\log Q\ge1$, $\log P\le\log Q$, $8192(\log\log Q+1)\le\eta\log P$ and $\mathrm{res}=\exp((\frac16-\eta)\log P-\frac13\log\log Q)\ge2$ (`mrtBaseResolution P Q η`). Let $j\in\mathbb N$ with $S_0$ in the band $[\mathrm{lo}_{j+1},\mathrm{up}_{j+1}]$ and $V_\nu$ in $[\mathrm{lo}_{j+2},\mathrm{up}_{j+2}]$; let $N\ge1$, $F$ multiplicative and bounded by $1$, and $T>0$. Then, with $D_N$ the dyadic polynomial of `mrtTypicalCoefficient J V F` and $\mathcal L$ = `mrtLaterLogClass S₀ (V ν) F P Q η j T` (the bundle's set of $t\in(-T,T]$ where the binned prime polynomials of $V_\nu$ are small and those of $S_0$ are not),
--
--   $$\int_{\mathcal L}|D_N|^2\le2816e\Big(\frac TN+1\Big)\Big(\sum_{V_\nu}\tfrac1{p^2}+\big(\sum_{V_\nu}\tfrac1{p^2}\big)^2+\frac2{(j+2)^2\,\mathrm{res}}\Big)+\Big(\frac TN+1\Big)\frac{1}{P\,(j+2)^2},$$
--
--   where $(j+2)^2\mathrm{res}$ is `mrtResolution P Q η (j+2)`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_later_log_class_energy`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open Set
open scoped Classical

theorem mrt_later_log_class_energy {ι : Type*} (J : Finset ι) (V : ι → Finset ℕ)
    (hprime : ∀ ν ∈ J, ∀ p ∈ V ν, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) V) {ν : ι} (hν : ν ∈ J)
    (S₀ : Finset ℕ) (hprime₀ : ∀ p ∈ S₀, p.Prime)
    {P Q η : ℝ} (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hPQ : Real.log P ≤ Real.log Q)
    (hη : 0 < η) (hη' : η ≤ 1/6)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (j : ℕ)
    (hrange₀ : ∀ p ∈ S₀, mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1))
    (hrange₁ : ∀ p ∈ V ν, mrtBandLower P Q (j+2) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+2))
    {N : ℕ} (hN : 0 < N) (F : ℕ → ℂ)
    (hF : Multiplicative F) (hFb : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in mrtLaterLogClass S₀ (V ν) F P Q η j T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*
        ((∑ p ∈ V ν, 1/(p:ℝ)^2)+(∑ p ∈ V ν, 1/(p:ℝ)^2)^2+
          2/mrtResolution P Q η (j+2)) +
      (T/N+1)*P⁻¹*(((j:ℝ)+2)^2)⁻¹ := by
  sorry

end OAI.TwoPointCorrelations
