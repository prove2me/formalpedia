-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_two_score_procedure
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:59:19.349198+00:00
-- url     : https://prove2.me/theorems/c5bc4320-385c-471d-87f2-c5193c8e7c32
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure` of [lean/OAI/Combinatorics/RamseyFive/Decoding/DimensionTwoProcedure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Decoding/DimensionTwoProcedure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence CellVariance ScoreRegularity`, `open MeasureTheory PoissonScore ParameterHierarchy Filter`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_two_score_procedure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [∀x : ℙ K V,Fintype (RadialLine x)],
--       ∀ {J : Type} [Fintype J] (X U S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
--         (ia ib ic : ℙ K V→J) (T : Finset (ℙ K (Dual K V))),
--         finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
--         0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆X → S⊆U → X.card≤4*S.card →
--         (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
--         (Nat.card K:ℝ)^3*Real.exp (-b)≤(X.card:ℝ)*T.card →
--         (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
--         (∀x,C (ic x)=C (ia x)∩C (ib x)) →
--         (S.card:ℝ)≤10*Real.exp (3*σ/2) →
--         (Nat.card K:ℝ)/S.card≤1/100 → (Nat.card K:ℝ)*P η σ D R≤S.card →
--         (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
--       Real.exp (-8*P η σ D R*τ)/4≤
--       (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
--         {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
--           (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*P η σ D R) ∧
--           (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P η σ D R) ∧
--           (9/10:ℝ)*S.card≤((W∩S).card:ℝ)}
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.PoissonScore.sampleCount`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength` and `OAI.SharpRamseyFive.ScoreRegularity.ownFraction` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.PoissonScore.emptyTests`, `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.decoded`, `OAI.SharpRamseyFive.ScoreGeometry.hyperplaneSupport` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Decoding/DimensionTwoProcedure.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure)

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory PoissonScore ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_score_procedure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (X U S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
      (ia ib ic : ℙ K V→J) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆X → S⊆U → X.card≤4*S.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (S.card:ℝ)≤10*Real.exp (3*σ/2) →
      (Nat.card K:ℝ)/S.card≤1/100 → (Nat.card K:ℝ)*P η σ D R≤S.card →
      (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
    Real.exp (-8*P η σ D R*τ)/4≤
    (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
      {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*P η σ D R) ∧
        (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P η σ D R) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ)} := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
