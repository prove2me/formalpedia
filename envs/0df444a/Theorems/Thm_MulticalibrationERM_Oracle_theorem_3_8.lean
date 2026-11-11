-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_theorem_3_8
-- name    : MulticalibrationERM.Oracle.theorem_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:51:53.135234+00:00
-- url     : https://prove2.me/theorems/1d569477-bde5-401e-a582-d21f84ae7ce1
-- title:
--   Theorem 3.8 — batch guarantee of Algorithm 1 (SignedTests)
-- statement:
--   There are absolute constants $C_0$ (the constant of $\mathrm{Reg}$, Theorem 2.5) and $C$ such that the following holds. Let $S\subseteq\{-1,+1\}^\Lambda$ be a list of $N$ tests with distortion $\kappa$, and let $\delta,\alpha\in(0,1]$. Let $(X_t,Y_t)_{t\le T}$ be independent draws from $D$, and run Algorithm 1 with any weighted ERM oracle for $H$, $\eta=\min\{1,\sqrt{\log N/T}\}$ and $L\ge2\alpha^{-2}\log(16mT/\delta)$. Then with probability at least $1-\delta$ the averaged predictor $\bar Q=T^{-1}\sum_tQ_t$ satisfies
--   $$\mathrm{MC}(\bar Q)\le\frac1{2K}+\kappa\Big[\frac1T\mathrm{Reg}\Big(T,d,\frac{\delta}{8N}\Big)+C\sqrt{\frac{d\log(eT)+\log(8N/\delta)}{T}}+\alpha\Big].$$
--
--   Differences from the source:
--   - encoding: C_0 the constant of Theorem 2.5 → C_0 existentially quantified with C before every instance; reason: the bound with a given C_0 implies it with every larger one, so this is the same claim
--   - encoding: T rounds → T ≥ 1; reason: nondegeneracy: the averaged predictor and Reg(T, ·) are undefined at T = 0
--   - encoding: rounds t = 1, …, T and examples (X_t, Y_t) → rounds t = 0, …, T − 1 reading the examples from an i.i.d. stream (seedMeasure), with Gaussians, uniforms and oracle seeds as further independent coordinates; reason: index shift and explicit randomness; same algorithm
--   - generalization: a class of VC dimension d (standing assumption, p. 12) → any class of VC dimension at most d (with d ≥ 1); reason: every class of VC dimension exactly d is an instance
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 20, Theorem 3.8

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_Forecast
import Definitions.Def_MulticalibrationERM_Oracle_SignedTests

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Theorem 3.8 (p. 20): batch guarantee of Algorithm 1. For a list `S` of `N` tests in
`{−1, +1}^Λ` with distortion `κ`, `δ, α ∈ (0, 1]`, `η = min{1, √(log N / T)}` and
`L ≥ 2α⁻² log(16mT/δ)`, on `T` i.i.d. examples from `D`, with probability at least `1 − δ` the
averaged predictor `Q̄ = T⁻¹ ∑_t Q_t` satisfies
`MC(Q̄) ≤ 1/(2K) + κ [T⁻¹ Reg(T, d, δ/(8N)) + C √((d log(eT) + log(8N/δ))/T) + α]`,
where `C₀` (inside `Reg`) is the absolute constant of Theorem 2.5 and `C` is absolute. -/
theorem theorem_3_8 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ), IsAuditorClass H d →
    ∀ (D : LabeledDist X) {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (O : ERMOracle X H 0 Ω) (K : ℕ), 1 ≤ K →
    ∀ (S : List (Fin (K + 1) → ℝ)) (κ : ℝ), (∀ σ ∈ S, ∀ v, σ v = 1 ∨ σ v = -1) →
      HasDistortion S κ →
    ∀ (δ α : ℝ), 0 < δ → δ ≤ 1 → 0 < α → α ≤ 1 →
    ∀ (T L : ℕ), 1 ≤ T → a1Lmin K T α δ ≤ L →
      seedMeasure D ν {ω | batchBound C₀ C K S.length κ d T δ α <
          gridMC D H K (signedTestsQbar O K ⟨S, T, a1Eta S.length T, L⟩ ω)} ≤
        ENNReal.ofReal δ := by sorry

end MulticalibrationERM.Oracle
