-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveRestriction_eventually_three_flat_finite_predictor
-- name    : OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:54:38.610711+00:00
-- url     : https://prove2.me/theorems/9aa567e6-474e-4801-a3bd-c1b44789028b
-- title:
--   OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor` of [lean/OAI/Combinatorics/RamseyFive/Geometry/ThreeFiniteOriented.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/ThreeFiniteOriented.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveRestriction`, with `open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy`, `open DyadicLifts ReverseCap Filter ParameterHierarchy`, `open scoped Classical LinearAlgebra.Projectivization NNReal Topology`):
--
--   ```lean
--   theorem eventually_three_flat_finite_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
--       ∀ (A : Submodule K V) (hA : finrank K A=4)
--         (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
--         finrank K V≤5 → Nat.card K=q → Real.exp σ=q →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
--         0<τ → τ≤σ^(-800*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
--         (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
--         (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
--         (X.card:ℝ)≤100*(X∩flatPoints A).card →
--         ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
--           let pred := threeFlatFinitePredictor A hA σ UX UT τ (P η σ D R) R L₀ k
--           let p := pred.output X T
--           p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
--           (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
--             (9/100000:ℝ)*X.card≤(W∩X).card) ∧
--           (∀t m,pred.encoded X T t=some m→pred.cost t m≤
--             30000*(Nat.card K:ℝ)*(P η σ D R)*
--               (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law` and `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta` and `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ProjectiveRestriction.threeFlatFinitePredictor` and `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor.output` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_finite_predictor` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/ThreeFiniteOriented.lean (declaration OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor)

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

section

attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_three_flat_finite_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (A : Submodule K V) (hA : finrank K A=4)
      (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K V≤5 → Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
        let pred := threeFlatFinitePredictor A hA σ UX UT τ (P η σ D R) R L₀ k
        let p := pred.output X T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/100000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,pred.encoded X T t=some m→pred.cost t m≤
          30000*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  sorry
end SharpRamseyFive.ProjectiveRestriction

end OAI
end
