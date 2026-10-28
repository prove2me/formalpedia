-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_two_score_integrals
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:59:11.317531+00:00
-- url     : https://prove2.me/theorems/0db3cfd6-5e90-4e8d-8887-bd8cf0926c40
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals` of [lean/OAI/Combinatorics/RamseyFive/Probability/DimensionTwoIntegrals.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Probability/DimensionTwoIntegrals.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory`, `open Filter ParameterHierarchy`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_two_score_integrals {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [∀x : ℙ K V,Fintype (RadialLine x)],
--       ∀ {J : Type} [Fintype J] (U S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
--         (ia ib ic : ℙ K V→J),
--         finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
--         τ≤σ^(-200*beta η) → S.Nonempty →
--         (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
--         (∀x,C (ic x)=C (ia x)∩C (ib x)) →
--         (S.card:ℝ)≤10*Real.exp (3*σ/2) →
--         (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
--         let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
--         let O := fun x => C (ia x)∪C (ib x)
--         let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
--         let t := scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
--         (∫ω,((typicalFailures S S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
--           (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) ∧
--         (∫ω,((typicalFailures U S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤(S.card:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength`, `OAI.SharpRamseyFive.ScoreRegularity.ownFraction` and `OAI.SharpRamseyFive.ScoreRegularity.scale` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.typicalFailures` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Probability/DimensionTwoIntegrals.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals)

import Mathlib
import Definitions.Def_OAIQ060R003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_score_integrals {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (U S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
      (ia ib ic : ℙ K V→J),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (S.card:ℝ)≤10*Real.exp (3*σ/2) →
      (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let O := fun x => C (ia x)∪C (ib x)
      let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
      let t := scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
      (∫ω,((typicalFailures S S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) ∧
      (∫ω,((typicalFailures U S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤(S.card:ℝ) := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
