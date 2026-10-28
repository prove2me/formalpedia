-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_three_training_score
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:58:25.279126+00:00
-- url     : https://prove2.me/theorems/bb3565e7-ca20-4b89-aa11-b5e45c7129ff
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score` of [lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionTwoPublic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionTwoPublic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial`, `open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory`, `open Filter ParameterHierarchy`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_three_training_score {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
--         [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
--         [∀x : ℙ K (I→K),Fintype (RadialLine x)],
--       ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
--         (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
--         Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
--         0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
--         (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
--         (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
--         (X.card:ℝ)=Real.exp (3*σ/2+g) →
--         100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) →
--         (∀j∈F,finrank K (Flat j)=3) →
--         (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
--       let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
--       let ht : 0<t := by positivity
--       let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
--       let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
--       let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
--       let a := queryPart F hF (fun j=>flatPoints (Flat j)) X m
--       (∀i,(C i).card≤(S.card:ℝ)/25) →
--       S⊆X ∧ X.card≤2*S.card ∧
--       Real.exp (-8*P η σ D R*τ)/4≤
--         (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
--           (trueScoreSuccess U S (fun x=>C (a x))
--             (fun x=>Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (a x)) ∅)))
--             (exceptional S C) R (2*(Nat.card K:ℝ)*P η σ D R)
--             ((S.card:ℝ)*Real.exp (10*P η σ D R)) ((9/10:ℝ)*S.card))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GreedyTraining.clippedPart`, `OAI.SharpRamseyFive.GreedyTraining.peelLength`, `OAI.SharpRamseyFive.GreedyTraining.peelSet`, `OAI.SharpRamseyFive.GreedyTraining.queryPart`, `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength` and `OAI.SharpRamseyFive.ScoreRegularity.ownFraction` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.trueScoreSuccess` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_small_protocol` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionTwoPublic.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score)

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
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_training_score {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (3*σ/2+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    let a := queryPart F hF (fun j=>flatPoints (Flat j)) X m
    (∀i,(C i).card≤(S.card:ℝ)/25) →
    S⊆X ∧ X.card≤2*S.card ∧
    Real.exp (-8*P η σ D R*τ)/4≤
      (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
        (trueScoreSuccess U S (fun x=>C (a x))
          (fun x=>Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (a x)) ∅)))
          (exceptional S C) R (2*(Nat.card K:ℝ)*P η σ D R)
          ((S.card:ℝ)*Real.exp (10*P η σ D R)) ((9/10:ℝ)*S.card)) := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
