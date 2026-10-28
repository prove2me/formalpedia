-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_literal_plane_half_exceptions
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:51:16.00954+00:00
-- url     : https://prove2.me/theorems/d25d7118-c8db-4886-9feb-a4efa3b29957
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions` of [lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionFourLowAmbient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionFourLowAmbient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial`, `open ParameterHierarchy Filter`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_literal_plane_half_exceptions {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
--       ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
--         [∀x : ℙ K (I→K),Fintype (RadialLine x)],
--       ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
--         (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
--         (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
--         (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
--         2<q → Nat.card K=q → Real.exp σ=q → (Fintype.card I=4 ∨ Fintype.card I=5) →
--         g≤2*σ → (∀j∈F,finrank K (Flat j)=3) →
--         (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
--         (X.card:ℝ)≤Real.exp (3*σ/2+g) →
--         t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5) →
--         S=peelSet (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
--         Real.exp (3*σ/2+g)/4≤S.card → (S.card:ℝ)≤Real.exp (3*σ) →
--         (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
--           (peelLength (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
--         (∀l∈Lines,finrank K l=2) →
--         let O' := fun x => S∩O x
--         ((radialExceptions S O' (pointStrength S) Lines Q q S.card (P η σ D R/200)).card:ℝ)≤
--           (S.card:ℝ)*Real.exp (-L η σ D/1000)/2 ∧
--         ((ambientHalfStrongExceptions σ (P η σ D R) S O' Lines Q).card:ℝ)≤
--           (S.card:ℝ)*Real.exp (7*P η σ D R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GreedyTraining.ownCell`, `OAI.SharpRamseyFive.GreedyTraining.peelLength`, `OAI.SharpRamseyFive.GreedyTraining.peelSet`, `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints`, `OAI.SharpRamseyFive.ScoreGeometry.ambientHalfStrongExceptions`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength` and `OAI.SharpRamseyFive.ScoreGeometry.radialExceptions` (definitions bundle `OAIQ060R001` of this split).
--
--   **Used by.** The proofs of `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_low_score_integrals` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_training_score` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionFourLowAmbient.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions)

import Mathlib
import Definitions.Def_OAIQ060R000
import Definitions.Def_OAIQ060R001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_literal_plane_half_exceptions {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
      (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
      2<q → Nat.card K=q → Real.exp σ=q → (Fintype.card I=4 ∨ Fintype.card I=5) →
      g≤2*σ → (∀j∈F,finrank K (Flat j)=3) →
      (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
      (X.card:ℝ)≤Real.exp (3*σ/2+g) →
      t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5) →
      S=peelSet (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
      Real.exp (3*σ/2+g)/4≤S.card → (S.card:ℝ)≤Real.exp (3*σ) →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
      (∀l∈Lines,finrank K l=2) →
      let O' := fun x => S∩O x
      ((radialExceptions S O' (pointStrength S) Lines Q q S.card (P η σ D R/200)).card:ℝ)≤
        (S.card:ℝ)*Real.exp (-L η σ D/1000)/2 ∧
      ((ambientHalfStrongExceptions σ (P η σ D R) S O' Lines Q).card:ℝ)≤
        (S.card:ℝ)*Real.exp (7*P η σ D R) := by
  sorry
end SharpRamseyFive.ScoreGeometry

end OAI
end
