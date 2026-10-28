-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_high_original_tail_retained
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:44.834991+00:00
-- url     : https://prove2.me/theorems/bfb6e234-14bd-4872-9593-ee19d37638c1
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained` of [lean/OAI/Combinatorics/RamseyFive/Geometry/UniformHighTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/UniformHighTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory`, `open Filter ParameterHierarchy`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_high_original_tail_retained {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
--       ∀ (x : ℙ K V) [Fintype (RadialLine x)],
--       ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
--         (F : Finset (ℙ K (Dual K V))) (t : ℝ),
--         finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
--         τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
--         (S.card:ℝ)≤10*Real.exp (5*σ/2) →
--         (Nat.card K:ℝ)^2*Real.exp (P η σ D R/20000)≤(S.card:ℝ) →
--         (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
--         (∀H∈F,Incident x H ∧ H∉exceptional S C) →
--         x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
--         ∀ (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)),
--         (∀l : RadialLine x,l.val∈Lines) → x∈Q →
--         (∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
--           x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
--             (((pointStrength S:ℝ)*2^i)/2) Lines Q
--             ((Nat.card K:ℝ)^4/S.card^2*Real.exp (P η σ D R/100)/
--               (((pointStrength S:ℝ)*2^i)/2)^100)) →
--         ((∑z : WeightedPrograms.DistinctPairs F,WeightedPrograms.strength (pencilLines x F)
--           (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
--           dyadFactor (outsideAt x S (C a∪C b)).card (P η σ D R/100)*
--             (geometryScale (Nat.card K) S.card)^2) →
--         x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
--           ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 →
--         geometryScale (Nat.card K) S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
--         (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
--           {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
--             (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
--           (Nat.card K:ℝ)^(-(50:ℝ))+
--         ∫ω,1-HighMoment.allTrunc R 5000 ω
--           ∂batchMeasure (fun i : Fin R×RadialLine x => L₀*
--             radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.batchMeasure`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GlobalRadial.badCenters`, `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ScoreGeometry.Unsampled`, `OAI.SharpRamseyFive.ScoreGeometry.boundedOverlapDyads`, `OAI.SharpRamseyFive.ScoreGeometry.dyadFactor`, `OAI.SharpRamseyFive.ScoreGeometry.geometryScale`, `OAI.SharpRamseyFive.ScoreGeometry.momentOrder`, `OAI.SharpRamseyFive.ScoreGeometry.outsideAt`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength`, `OAI.SharpRamseyFive.ScoreRegularity.ownFraction`, `OAI.SharpRamseyFive.WeightedPrograms.DistinctPairs`, `OAI.SharpRamseyFive.WeightedPrograms.flat_HighMomentRecovered_7` and `OAI.SharpRamseyFive.WeightedPrograms.strength` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.HighMoment.allTrunc` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.pencilLines`, `OAI.SharpRamseyFive.ScoreGeometry.pointScore`, `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ScoreRegularity.irregular` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proofs of `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_score_integrals` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/UniformHighTail.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_high_original_tail_retained {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (5*σ/2) →
      (Nat.card K:ℝ)^2*Real.exp (P η σ D R/20000)≤(S.card:ℝ) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
      ∀ (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)),
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      (∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
        x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
          (((pointStrength S:ℝ)*2^i)/2) Lines Q
          ((Nat.card K:ℝ)^4/S.card^2*Real.exp (P η σ D R/100)/
            (((pointStrength S:ℝ)*2^i)/2)^100)) →
      ((∑z : WeightedPrograms.DistinctPairs F,WeightedPrograms.strength (pencilLines x F)
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
        dyadFactor (outsideAt x S (C a∪C b)).card (P η σ D R/100)*
          (geometryScale (Nat.card K) S.card)^2) →
      x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
        ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 →
      geometryScale (Nat.card K) S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ))+
      ∫ω,1-HighMoment.allTrunc R 5000 ω
        ∂batchMeasure (fun i : Fin R×RadialLine x => L₀*
          radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2) := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
