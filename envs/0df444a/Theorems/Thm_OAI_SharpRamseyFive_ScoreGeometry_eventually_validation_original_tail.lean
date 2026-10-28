-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_validation_original_tail
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:06:21.365588+00:00
-- url     : https://prove2.me/theorems/c89a900a-d76e-4bf8-b367-27841e04d0ee
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail` of [lean/OAI/Combinatorics/RamseyFive/Probability/UniformTails.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Probability/UniformTails.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory`, `open Filter ParameterHierarchy`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_validation_original_tail {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (d : ℕ) (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
--       ∀ (x : ℙ K V) [Fintype (RadialLine x)],
--       ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
--         (F : Finset (ℙ K (Dual K V))) (t : ℝ),
--         finrank K V=d+1 → 2≤d → d≤4 → (Nat.card K:ℝ)=Real.exp σ →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
--         τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
--         (S.card:ℝ)≤10*Real.exp (((d:ℝ)+1)*σ/2) →
--         (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
--         (∀H∈F,Incident x H ∧ H∉exceptional S C) →
--         x∉irregular (d:=d) S C ((L₀:ℝ)/100) →
--         (∀u:ℝ,0<u → u≤2 →
--           ((Finset.univ.filter fun z:{z : F × F // z.1≠z.2} =>
--             u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
--               (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*u^200≤
--             (scale (K:=K) d S.card)^2*Real.exp (P η σ D R/50)) →
--         scale (K:=K) d S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
--         (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
--           {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
--             (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
--           Real.exp (-P η σ D R/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.mass`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ScoreGeometry.Unsampled`, `OAI.SharpRamseyFive.ScoreGeometry.outsideAt`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength`, `OAI.SharpRamseyFive.ScoreRegularity.ownFraction` and `OAI.SharpRamseyFive.ScoreRegularity.scale` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.pencilLines`, `OAI.SharpRamseyFive.ScoreGeometry.pointScore`, `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ScoreRegularity.irregular` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proofs of `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_low_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_score_integrals`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_three_validation_tail` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Probability/UniformTails.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_validation_original_tail {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (d : ℕ) (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=d+1 → 2≤d → d≤4 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (((d:ℝ)+1)*σ/2) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=d) S C ((L₀:ℝ)/100) →
      (∀u:ℝ,0<u → u≤2 →
        ((Finset.univ.filter fun z:{z : F × F // z.1≠z.2} =>
          u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
            (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*u^200≤
          (scale (K:=K) d S.card)^2*Real.exp (P η σ D R/50)) →
      scale (K:=K) d S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        Real.exp (-P η σ D R/2) := by
  sorry

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end
