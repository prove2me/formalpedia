-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_proposition_6_8
-- name    : MulticalibrationERM.Oracle.proposition_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:51:54.919525+00:00
-- url     : https://prove2.me/theorems/af6ced44-6f14-4b60-a2b8-ac838eb002fa
-- title:
--   Proposition 6.8 — batch guarantee of Algorithm 1 with valid interval hints
-- statement:
--   Under the conditions of Theorem 3.8 (same absolute constants $C_0$, $C$ in form), let $O$ be a finite set of inputs with intervals $I_x=[ylo_x,yhi_x]\subseteq[0,1]$ that are fixed independently of the examples and valid ($f^\star(x)\in I_x$). Then the conclusion of Theorem 3.8 holds for Algorithm 1 with interval hints (forecasts $\mathrm{Minimax}_{\Lambda_x}$, $\Lambda_x=\Lambda\cap[\lfloor K\,ylo_x\rfloor/K,\lceil K\,yhi_x\rceil/K]$ for $x\in O$, $\Lambda_x=\Lambda$ otherwise): with probability at least $1-\delta$,
--   $$\mathrm{MC}(\bar Q)\le\frac1{2K}+\kappa\Big[\frac1T\mathrm{Reg}\Big(T,d,\frac{\delta}{8N}\Big)+C\sqrt{\frac{d\log(eT)+\log(8N/\delta)}{T}}+\alpha\Big].$$
--
--   Differences from the source:
--   - encoding: intervals fixed independently of the examples; the conclusion holds conditionally on the intervals → the statement for every fixed (deterministic) family of valid intervals; reason: conditioning on independent intervals is the statement for each of their values
--   - reading: f⋆(x) = E[Y | X = x] for x ∈ O → the condition f⋆(x) ∈ I_x is imposed (or asserted) at the inputs x ∈ O with D_X({x}) > 0; f⋆ is defined at atoms as E[Y 1{X = x}]/D_X({x}); reason: a conditional mean is determined only up to D_X-null sets, so at an input of mass zero its value is not determined; at atoms it is
--   - encoding: T rounds → T ≥ 1; reason: nondegeneracy: the averaged predictor and Reg(T, ·) are undefined at T = 0
--   - encoding: rounds t = 1, …, T and examples (X_t, Y_t) → rounds t = 0, …, T − 1 reading the examples from an i.i.d. stream (seedMeasure), with Gaussians, uniforms and oracle seeds as further independent coordinates; reason: index shift and explicit randomness; same algorithm
--   - generalization: a class of VC dimension d (standing assumption, p. 12) → any class of VC dimension at most d (with d ≥ 1); reason: every class of VC dimension exactly d is an instance
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 35, Proposition 6.8

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_Forecast
import Definitions.Def_MulticalibrationERM_Oracle_SignedTests

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Proposition 6.8 (p. 35): batch guarantee with interval hints. Under the conditions of
Theorem 3.8, let the intervals `I_x = [ylo_x, yhi_x] ⊆ [0, 1]`, `x ∈ O`, be fixed (independent of
the examples) and valid (`f⋆(x) ∈ I_x`). Then the conclusion of Theorem 3.8 holds for Algorithm 1
with interval hints, whose forecast at `x` is the minimax forecast on
`Λ_x = Λ ∩ [⌊K ylo_x⌋/K, ⌈K yhi_x⌉/K]` for `x ∈ O` and on `Λ` otherwise. Validity is required at
the inputs of positive mass, where `f⋆(x) = E[Y | X = x]` is determined. -/
theorem proposition_6_8 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ {X : Type} [MeasurableSpace X] [DecidableEq X] (H : Set (X → Bool)) (d : ℕ),
      IsAuditorClass H d →
    ∀ (D : LabeledDist X) {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (O : ERMOracle X H 0 Ω) (K : ℕ), 1 ≤ K →
    ∀ (S : List (Fin (K + 1) → ℝ)) (κ : ℝ), (∀ σ ∈ S, ∀ v, σ v = 1 ∨ σ v = -1) →
      HasDistortion S κ →
    ∀ (δ α : ℝ), 0 < δ → δ ≤ 1 → 0 < α → α ≤ 1 →
    ∀ (T L : ℕ), 1 ≤ T → a1Lmin K T α δ ≤ L →
    ∀ (Oset : Finset X) (ylo yhi : X → ℝ),
      (∀ x ∈ Oset, 0 ≤ ylo x ∧ ylo x ≤ yhi x ∧ yhi x ≤ 1) →
      (∀ x ∈ Oset, 0 < D.atom x → D.fstar x ∈ Set.Icc (ylo x) (yhi x)) →
      seedMeasure D ν {ω | batchBound C₀ C K S.length κ d T δ α <
          gridMC D H K (a1Qbar O K ⟨S, T, a1Eta S.length T, L⟩
            (hintLo K Oset ylo) (hintHi K Oset yhi) 0 ω)} ≤
        ENNReal.ofReal δ := by sorry

end MulticalibrationERM.Oracle
