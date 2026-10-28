-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_captured_global_trunc_exp_bound
-- name    : OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:56:14.396519+00:00
-- url     : https://prove2.me/theorems/f9dc6d34-31c5-4046-a7e2-798d7812ed0c
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound` of [lean/OAI/Combinatorics/RamseyFive/Geometry/HighGeometryClosure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HighGeometryClosure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal`):
--
--   ```lean
--   theorem captured_global_trunc_exp_bound (hdim : finrank K V=5)
--       {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
--       (Flat : I→Submodule K V) (X S : Finset (ℙ K V))
--       (hFlat : ∀ i∈F,finrank K (Flat i)=3) (j : ℕ)
--       (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
--       (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
--       (O : ℙ K V→Finset (ℙ K V))
--       (hO : ∀ x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
--       (δ L : ℝ≥0) (hδ : 0<δ) (σ g n : ℝ) (hσ : 1≤σ)
--       (hq : (Nat.card K:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g))
--       (hg : g≤σ) (hX : (X.card:ℝ)≤n) (hscale : n*(δ:ℝ)≤4*Nat.card K)
--       (hcut : 8*(δ:ℝ)*(j+1)≤2*Real.exp (-(g+σ/2)/20))
--       (Lines : Finset (Submodule K V)) (hrank : ∀ l∈Lines,finrank K l=2)
--       (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
--       (R : ℕ) :
--       (∑ x : Q,∫ ω,1-HighMoment.allTrunc R 5000 ω
--         ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
--           L*radialWeight x.val (outsideAt x.val S (O x.val)) δ p.2)) ≤
--         globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
--         globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*σ*Real.exp (2*σ-4998*g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.batchMeasure` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GreedyTraining.ownCell`, `OAI.SharpRamseyFive.GreedyTraining.remaining`, `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints`, `OAI.SharpRamseyFive.ScoreGeometry.globalTruncConstant` and `OAI.SharpRamseyFive.ScoreGeometry.outsideAt` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.HighMoment.allTrunc` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HighGeometryClosure.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound)

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

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)]
  [∀ x : ℙ K V,Fintype (RadialLine x)]

theorem captured_global_trunc_exp_bound (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V))
    (hFlat : ∀ i∈F,finrank K (Flat i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀ x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
    (δ L : ℝ≥0) (hδ : 0<δ) (σ g n : ℝ) (hσ : 1≤σ)
    (hq : (Nat.card K:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hg : g≤σ) (hX : (X.card:ℝ)≤n) (hscale : n*(δ:ℝ)≤4*Nat.card K)
    (hcut : 8*(δ:ℝ)*(j+1)≤2*Real.exp (-(g+σ/2)/20))
    (Lines : Finset (Submodule K V)) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (R : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val S (O x.val)) δ p.2)) ≤
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*σ*Real.exp (2*σ-4998*g) := by
  sorry

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end
