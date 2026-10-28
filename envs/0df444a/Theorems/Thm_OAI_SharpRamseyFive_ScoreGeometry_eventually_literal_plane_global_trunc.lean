-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_literal_plane_global_trunc
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:57:42.812996+00:00
-- url     : https://prove2.me/theorems/7abf80ae-7766-4ed8-bcd2-6879bee2e21b
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc` of [lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore`, `open Filter ParameterHierarchy MeasureTheory`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_literal_plane_global_trunc {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ) (L₀ : ℝ≥0),Range η σ D R → (L₀:ℝ)=L η σ D →
--       ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
--         [Fintype (ℙ K (I→K))] [∀x : ℙ K (I→K),Fintype (RadialLine x)],
--       ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
--         (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
--         (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
--         (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
--         2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
--         P η σ D R/10000≤g → g≤σ →
--         (∀j∈F,finrank K (Flat j)=3) →
--         (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
--         (X.card:ℝ)≤Real.exp (2*σ+g) →
--         t=(Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5) →
--         S=peelSet (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
--         Real.exp (2*σ+g)/4≤S.card → (q:ℝ)^2≤S.card →
--         (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
--           (peelLength (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
--         (∀l∈Lines,finrank K l=2) → (∀x∈Q,∀l : RadialLine x,l.val∈Lines) →
--       (∑x : Q,∫ω,1-HighMoment.allTrunc R 5000 ω
--         ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
--           L₀*radialWeight x.val (outsideAt x.val S (S∩O x.val)) (pointStrength S) p.2))≤Real.exp (2*σ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.batchMeasure` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GreedyTraining.ownCell`, `OAI.SharpRamseyFive.GreedyTraining.peelLength`, `OAI.SharpRamseyFive.GreedyTraining.peelSet`, `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints`, `OAI.SharpRamseyFive.ScoreGeometry.outsideAt` and `OAI.SharpRamseyFive.ScoreGeometry.pointStrength` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.HighMoment.allTrunc` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc)

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

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_literal_plane_global_trunc {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ) (L₀ : ℝ≥0),Range η σ D R → (L₀:ℝ)=L η σ D →
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
      (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      P η σ D R/10000≤g → g≤σ →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
      (X.card:ℝ)≤Real.exp (2*σ+g) →
      t=(Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5) →
      S=peelSet (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
      Real.exp (2*σ+g)/4≤S.card → (q:ℝ)^2≤S.card →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
      (∀l∈Lines,finrank K l=2) → (∀x∈Q,∀l : RadialLine x,l.val∈Lines) →
    (∑x : Q,∫ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L₀*radialWeight x.val (outsideAt x.val S (S∩O x.val)) (pointStrength S) p.2))≤Real.exp (2*σ) := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
