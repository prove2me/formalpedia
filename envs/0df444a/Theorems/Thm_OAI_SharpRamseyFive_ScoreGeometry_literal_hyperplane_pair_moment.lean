-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_literal_hyperplane_pair_moment
-- name    : OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:59:34.723993+00:00
-- url     : https://prove2.me/theorems/123f96e8-8694-4b6b-86c1-b7032fc711fd
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment` of [lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget GlobalRadial PoissonScore WeightedPrograms`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal`):
--
--   ```lean
--   theorem literal_hyperplane_pair_moment [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] (hdim : finrank K V=5)
--       (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K V)
--       (X XH S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
--       (Planes : Finset (Submodule K V)) (hPlanes : ∀A∈Planes,finrank K A=3)
--       (hcomplete : ∀A : Submodule K V,finrank K A=3 → A∈Planes)
--       (e : Prop) (_he : e)
--       (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
--       (hS : S⊆XH) (x : ℙ K V) [Fintype (RadialLine x)]
--       (hO : ownCell F hF (fun i=>flatPoints (Flat i)) X
--         (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) x⊆O x)
--       (G : Finset (ℙ K (Dual K V))) (hG : ∀H∈G,Incident x H)
--       (χ : ℝ) (hχ : (34359738369*2^200:ℝ)≤Real.exp χ)
--       (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
--       (hscale : (X.card:ℝ)*(pointStrength (K:=K) S:ℝ)≤4*Nat.card K)
--       (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card)
--       (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
--       (Q : Finset (ℙ K V)) (hxQ : x∈Q)
--       (hm : ∀H : G,mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x G H)≤2)
--       (hgood : x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) X.card χ)
--       (hpair : x∉hyperplanePeelExceptions F hF Flat X XH S Planes
--         (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) (pointStrength S) χ Q) :
--       (∑z : DistinctPairs G,strength (pencilLines x G)
--         (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
--         dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) S.card)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.mass`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GreedyTraining.ownCell`, `OAI.SharpRamseyFive.GreedyTraining.peelLength`, `OAI.SharpRamseyFive.GreedyTraining.peelSet`, `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints`, `OAI.SharpRamseyFive.ScoreGeometry.dyadFactor`, `OAI.SharpRamseyFive.ScoreGeometry.geometryScale`, `OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions`, `OAI.SharpRamseyFive.ScoreGeometry.outsideAt`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength`, `OAI.SharpRamseyFive.ScoreGeometry.radialExceptions`, `OAI.SharpRamseyFive.WeightedPrograms.DistinctPairs`, `OAI.SharpRamseyFive.WeightedPrograms.flat_HighMomentRecovered_7` and `OAI.SharpRamseyFive.WeightedPrograms.strength` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ScoreGeometry.pencilLines` and `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proofs of `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_score_integrals` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment)

import Mathlib
import Definitions.Def_OAIQ060R003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [LinearOrder J]

theorem literal_hyperplane_pair_moment [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] (hdim : finrank K V=5)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K V)
    (X XH S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Planes : Finset (Submodule K V)) (hPlanes : ∀A∈Planes,finrank K A=3)
    (hcomplete : ∀A : Submodule K V,finrank K A=3 → A∈Planes)
    (e : Prop) (_he : e)
    (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
    (hS : S⊆XH) (x : ℙ K V) [Fintype (RadialLine x)]
    (hO : ownCell F hF (fun i=>flatPoints (Flat i)) X
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) x⊆O x)
    (G : Finset (ℙ K (Dual K V))) (hG : ∀H∈G,Incident x H)
    (χ : ℝ) (hχ : (34359738369*2^200:ℝ)≤Real.exp χ)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(pointStrength (K:=K) S:ℝ)≤4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hm : ∀H : G,mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x G H)≤2)
    (hgood : x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) X.card χ)
    (hpair : x∉hyperplanePeelExceptions F hF Flat X XH S Planes
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) (pointStrength S) χ Q) :
    (∑z : DistinctPairs G,strength (pencilLines x G)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) S.card)^2 := by
  sorry

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end
