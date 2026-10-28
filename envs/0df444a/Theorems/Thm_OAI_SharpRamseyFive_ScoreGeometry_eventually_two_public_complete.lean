-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_two_public_complete
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:59:11.351222+00:00
-- url     : https://prove2.me/theorems/0afd8622-b2b3-43f6-837f-688790f78c68
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete` of [lean/OAI/Combinatorics/RamseyFive/Geometry/TwoPublic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/TwoPublic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy`, `open scoped Classical LinearAlgebra.Projectivization NNReal Topology`):
--
--   ```lean
--   theorem eventually_two_public_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))]
--         [∀x : ℙ K V,Fintype (RadialLine x)]
--         [∀x : ℙ K (Dual K V),Fintype (RadialLine x)],
--       ∀ (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (_hT : T.Nonempty),
--         finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
--         0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → T⊆UT →
--         (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
--         (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
--         ∃ n : Fin (1000*(Nat.card K)^2+1),
--           n.val=reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) ∧
--           let P₀ := P η σ D R
--           let H := 1000*(Nat.card K)^2
--           let encode := twoPublicEncoded S U T UT P₀ τ H n (Nat.card K)
--             ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card) ((T.card:ℝ)*Real.exp (2*P₀))
--           let decode := twoPublicDecoded U UT P₀ τ H (Nat.card K)
--           let p := map (twoPublicLaw U UT P₀ τ R L₀ H (Nat.card K))
--             (fun t=>(encode t).map (decode t))
--           p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
--           (∀W,0<p (some W)→ValidCap S U ((S.card:ℝ)*Real.exp (2*P₀)) W) ∧
--           (∀t m,encode t=some m → twoPublicCost U UT P₀ τ H (Nat.card K) t m≤
--             1300*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P₀))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.map` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ReverseCap.FreshIndex`, `OAI.SharpRamseyFive.ReverseCap.FreshTape`, `OAI.SharpRamseyFive.ReverseCap.UniversalFresh`, `OAI.SharpRamseyFive.ReverseCap.ValidCap`, `OAI.SharpRamseyFive.ReverseCap.cardCutoff`, `OAI.SharpRamseyFive.ReverseCap.reverseLength`, `OAI.SharpRamseyFive.ScoreGeometry.BaseMessage`, `OAI.SharpRamseyFive.ScoreGeometry.BaseTable`, `OAI.SharpRamseyFive.ScoreGeometry.ReversedBaseTape`, `OAI.SharpRamseyFive.ScoreGeometry.TwoPublicMessage`, `OAI.SharpRamseyFive.ScoreGeometry.TwoPublicTape`, `OAI.SharpRamseyFive.ScoreGeometry.baseAlphabet`, `OAI.SharpRamseyFive.ScoreGeometry.instFintypeBaseAlphabet` and `OAI.SharpRamseyFive.ScoreGeometry.twoPublicCost` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ScoreGeometry.twoPublicDecoded`, `OAI.SharpRamseyFive.ScoreGeometry.twoPublicEncoded` and `OAI.SharpRamseyFive.ScoreGeometry.twoPublicLaw` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_finite_predictor` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/TwoPublic.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete)

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
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_two_public_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [∀x : ℙ K V,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K V),Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (_hT : T.Nonempty),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → T⊆UT →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      ∃ n : Fin (1000*(Nat.card K)^2+1),
        n.val=reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) ∧
        let P₀ := P η σ D R
        let H := 1000*(Nat.card K)^2
        let encode := twoPublicEncoded S U T UT P₀ τ H n (Nat.card K)
          ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card) ((T.card:ℝ)*Real.exp (2*P₀))
        let decode := twoPublicDecoded U UT P₀ τ H (Nat.card K)
        let p := map (twoPublicLaw U UT P₀ τ R L₀ H (Nat.card K))
          (fun t=>(encode t).map (decode t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→ValidCap S U ((S.card:ℝ)*Real.exp (2*P₀)) W) ∧
        (∀t m,encode t=some m → twoPublicCost U UT P₀ τ H (Nat.card K) t m≤
          1300*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  sorry
end SharpRamseyFive.ScoreGeometry

end OAI
end
