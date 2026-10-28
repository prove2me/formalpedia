-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_hyperplanePeelExceptions_card
-- name    : OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:48:34.461773+00:00
-- url     : https://prove2.me/theorems/b5782588-e037-4d6b-87cf-d2647a147d64
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card` of [lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget GlobalRadial PoissonScore WeightedPrograms`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal`):
--
--   ```lean
--   theorem hyperplanePeelExceptions_card (F : Finset J) (hF : F.Nonempty)
--       (Flat : J→Submodule K V) (X XH S : Finset (ℙ K V))
--       (Planes : Finset (Submodule K V))
--       (hFlat : ∀i∈F,finrank K (Flat i)=4)
--       (hcover : ∀H : Submodule K V,finrank K H=4 → ∃i∈F,Flat i=H)
--       (hPlanes : ∀A∈Planes,finrank K A=3)
--       (e : Prop) (he : e)
--       (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
--       (hS : S⊆XH) (δ : ℝ≥0) (hδ : 0<δ) (χ g : ℝ) (hg : 0≤g) (hχ : 0≤χ)
--       (hn : (X.card:ℝ)=(Nat.card K:ℝ)^2*Real.exp g)
--       (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
--       (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
--       (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card) (Q : Finset (ℙ K V)) :
--       ((hyperplanePeelExceptions F hF Flat X XH S Planes
--         (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) δ χ Q).card:ℝ)≤
--         X.card*((Nat.clog 2 S.card:ℝ)+1)*(3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.GreedyTraining.peelLength`, `OAI.SharpRamseyFive.GreedyTraining.peelSet`, `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints` and `OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions` (definitions bundle `OAIQ060R001` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_peel_exceptions` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/HyperplaneHigh.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card)

import Mathlib
import Definitions.Def_OAIQ060R001

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

theorem hyperplanePeelExceptions_card (F : Finset J) (hF : F.Nonempty)
    (Flat : J→Submodule K V) (X XH S : Finset (ℙ K V))
    (Planes : Finset (Submodule K V))
    (hFlat : ∀i∈F,finrank K (Flat i)=4)
    (hcover : ∀H : Submodule K V,finrank K H=4 → ∃i∈F,Flat i=H)
    (hPlanes : ∀A∈Planes,finrank K A=3)
    (e : Prop) (he : e)
    (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
    (hS : S⊆XH) (δ : ℝ≥0) (hδ : 0<δ) (χ g : ℝ) (hg : 0≤g) (hχ : 0≤χ)
    (hn : (X.card:ℝ)=(Nat.card K:ℝ)^2*Real.exp g)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card) (Q : Finset (ℙ K V)) :
    ((hyperplanePeelExceptions F hF Flat X XH S Planes
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) δ χ Q).card:ℝ)≤
      X.card*((Nat.clog 2 S.card:ℝ)+1)*(3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)) := by
  sorry

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end
