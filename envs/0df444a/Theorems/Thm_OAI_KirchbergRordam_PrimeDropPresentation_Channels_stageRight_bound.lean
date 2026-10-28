-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_Channels_stageRight_bound
-- name    : OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:37:01.619992+00:00
-- url     : https://prove2.me/theorems/ad9beaf2-a9a6-4d23-8644-73d5021539a9
-- title:
--   OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound` of [lean/OAI/Analysis/CharacterCriterion/PrimeChannels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeChannels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.PrimeDropPresentation.Channels`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open MatrixDiagonalPath DiagonalIteration PrimeDropPresentation.Iteration`, `open GeneralDropSystem DropChannels`, `open BalancedDropSystem (half)`, `open MultiplicativeChannel (Channel)`, `open scoped CStarAlgebra ComplexOrder`, `open Filter Topology`):
--
--   ```lean
--   lemma stageRight_bound (n k : ℕ) (x : S.Stage n) {ε : ℝ} (hε : 0≤ε)
--       (hp : ∀ t : unitInterval,
--         ‖conj (star (normalizedPath S n k t))
--           ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
--           (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
--       (hf : ∀ t : unitInterval,
--         ‖conj (star (finalPath S n k t))
--           ((S.chain.map n (n+k+1) (by omega) x).val t)-
--           (S.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
--       (d : DimensionDrop23) :
--       ‖stageRight S n k d * (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x)-
--         (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x) * stageRight S n k d‖≤8*ε*‖d‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.MultiplicativeChannel.Channel` (definitions bundle `OAIB3Kr001` of this split); `OAI.KirchbergRordam.M6` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.DiagonalIteration.conj` (definitions bundle `OAIB3Kr008` of this split); `OAI.KirchbergRordam.DimensionDrop23` and `OAI.KirchbergRordam.dropSubringClass` (definitions bundle `OAIB3Kr010` of this split); `OAI.KirchbergRordam.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23`, `OAI.KirchbergRordam.PrimeDropPresentation.Channels.finalPath` and `OAI.KirchbergRordam.PrimeDropPresentation.Iteration.normalizedPath` (definitions bundle `OAIB3Kr013` of this split); `OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight` (definitions bundle `OAIB3Kr015` of this split); `OAI.KirchbergRordam.PrimeDropPresentation`, `OAI.KirchbergRordam.PrimeDimensionDrop.Algebra`, `OAI.KirchbergRordam.PrimeDimensionDrop.Fiber`, `OAI.KirchbergRordam.PrimeDropPresentation.Stage`, `OAI.KirchbergRordam.PrimeDropPresentation.chain`, `OAI.KirchbergRordam.PrimeDropPresentation.instCStarAlgebraStage`, `OAI.KirchbergRordam.CStarInductiveLimit.Chain` and `OAI.KirchbergRordam.CStarInductiveLimit.Chain.map` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.PrimeDropPresentation.Channels.finite_control` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeChannels.lean (declaration OAI.KirchbergRordam.PrimeDropPresentation.Channels.stageRight_bound)

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation.Channels
open MatrixDiagonalPath DiagonalIteration PrimeDropPresentation.Iteration
open GeneralDropSystem DropChannels
open BalancedDropSystem (half)
variable (S : PrimeDropPresentation)
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology

lemma stageRight_bound (n k : ℕ) (x : S.Stage n) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
    (hf : ∀ t : unitInterval,
      ‖conj (star (finalPath S n k t))
        ((S.chain.map n (n+k+1) (by omega) x).val t)-
        (S.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
    (d : DimensionDrop23) :
    ‖stageRight S n k d * (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x)-
      (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x) * stageRight S n k d‖≤8*ε*‖d‖ := by
  sorry
end KirchbergRordam.PrimeDropPresentation.Channels
end

end OAI
end
