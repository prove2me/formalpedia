-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_oriented_ready_encoded_failure
-- name    : OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:06.804599+00:00
-- url     : https://prove2.me/theorems/516dc963-7d09-4094-8585-87d92cf28802
-- title:
--   OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure` of [lean/OAI/Combinatorics/RamseyFive/Entropy/ReadyFailure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/ReadyFailure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveIncidence`, with `open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy`, `open scoped Classical LinearAlgebra.Projectivization NNReal Topology`):
--
--   ```lean
--   theorem eventually_oriented_ready_encoded_failure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))],
--       ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
--         (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
--         (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
--         Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
--         0≤b → b≤Cb*D*σ^(6*beta η) →
--         OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
--         (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
--         let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
--         let r := fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ UB
--           (UA.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
--         eventMass (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K))
--           (Finset.univ.filter (fun t => orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
--             (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t = none)) ≤
--               5*Real.exp (-(Nat.card K:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.eventMass`, `OAI.SharpRamseyFive.ProjectiveIncidence.bidualPoint` and `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta` and `OAI.SharpRamseyFive.ProjectiveIncidence.actualReadyFailurePropDecidable` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedNodeMessage`, `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedNodeTape`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeLaw` and `OAI.SharpRamseyFive.ScoreGeometry.fourFinitePredictor` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.OriginalNodeReady` and `OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNodeEncoded` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/ReadyFailure.lean (declaration OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure)

import Mathlib
import Definitions.Def_OAIQ060R004

section

attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
noncomputable section

local instance (priority := high) actualReadyFailurePropDecidable_r8d79b8_1 (P : Prop) : Decidable P := Classical.propDecidable P
theorem eventually_oriented_ready_encoded_failure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ UB
        (UA.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      eventMass (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K))
        (Finset.univ.filter (fun t => orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
          (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t = none)) ≤
            5*Real.exp (-(Nat.card K:ℝ)) := by
  sorry
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end
