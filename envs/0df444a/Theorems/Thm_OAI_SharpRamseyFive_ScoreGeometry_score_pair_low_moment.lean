-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_score_pair_low_moment
-- name    : OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:59:43.844967+00:00
-- url     : https://prove2.me/theorems/fd25776c-7a55-4755-bdfb-8e3d05a9ea67
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment` of [lean/OAI/Combinatorics/RamseyFive/Geometry/OutsideCard.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/OutsideCard.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators NNReal`, `open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal`):
--
--   ```lean
--   theorem score_pair_low_moment (hdim : finrank K V=5)
--       (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
--       (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
--       (n χ : ℝ) (hn : 0<n) (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
--       (hlow : n ≤ (Nat.card K:ℝ)^2*Real.exp (χ/2))
--       (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
--       (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
--       (Q : Finset (ℙ K V)) (hx : x∈Q)
--       (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
--       (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
--         x∉badCenters S O δ (((δ:ℝ)*2^i)/2) L Q
--           ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
--       (R : ℕ) (hR : 200 ≤ R) :
--       (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p^R) ≤
--         2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/n)^2*Real.exp (2*χ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.mass`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GlobalRadial.badCenters`, `OAI.SharpRamseyFive.ScoreGeometry.boundedOverlapDyads`, `OAI.SharpRamseyFive.ScoreGeometry.outsideAt`, `OAI.SharpRamseyFive.WeightedPrograms.DistinctPairs`, `OAI.SharpRamseyFive.WeightedPrograms.flat_HighMomentRecovered_7` and `OAI.SharpRamseyFive.WeightedPrograms.strength` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ScoreGeometry.pencilLines` and `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_ambient_tail` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_training_score` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/OutsideCard.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment)

import Mathlib
import Definitions.Def_OAIQ060R003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_low_moment (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n χ : ℝ) (hn : 0<n) (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hlow : n ≤ (Nat.card K:ℝ)^2*Real.exp (χ/2))
    (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) L Q
        ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/n)^2*Real.exp (2*χ)) := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
