-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_log_energy_partition_bound
-- name    : OAI.TwoPointCorrelations.mrt_log_energy_partition_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:38.938293+00:00
-- url     : https://prove2.me/theorems/2d5d3d9a-7e5e-4137-a8f5-ea4511f67dda
-- title:
--   Removing the small-value frequency bands costs little in the mean square of the typical dyadic polynomial
-- statement:
--   Let $V_1,\dots,V_J$ be pairwise disjoint sets of primes with $V_j$ inside the band $[\mathrm{lo}_j,\mathrm{up}_j]$ (`mrtBandLower P Q j`, `mrtBandUpper Q j`), for reals $P,Q>0$ with $\log P\ge2$, $\log Q\ge1$, $\log P\le\log Q$, and $\eta\in(0,1/12]$ with $8192(\log\log Q+1)\le\eta\log P$ and $\mathrm{res}$ = `mrtBaseResolution P Q η` $\ge2$. Let $N\ge1$ with $2Q\le N$, $F$ multiplicative and bounded by $1$, $T>0$, and $D_N$ the dyadic polynomial of `mrtTypicalCoefficient (Icc 1 J) V F`. Then
--
--   $$\int_{-T}^T|D_N|^2\le\int_{(-T,T]\cap\mathcal B}|D_N|^2+\frac{33792e(\frac TN+1)}{\mathrm{res}}+\frac{1024e^2(\frac{TQ}N+1)}{\mathrm{res}}+\frac{2(\frac TN+1)}P,$$
--
--   where $\mathcal B$ = `mrtNoSmallBand (mrtLogFamilyBins P Q η) (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J` is the set of $t$ lying in none of the first $J$ small-frequency bands (a band $r$ consists of the $t$ at which every binned prime polynomial of $V_{r+1}$ is below its threshold).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_log_energy_partition_bound`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open Set
open scoped Classical

theorem mrt_log_energy_partition_bound (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      (∫ t in Ioc (-T) T ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) +
      (33792*Real.exp 1*(T/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      2*(T/N+1)*P⁻¹) := by
  sorry

end OAI.TwoPointCorrelations
