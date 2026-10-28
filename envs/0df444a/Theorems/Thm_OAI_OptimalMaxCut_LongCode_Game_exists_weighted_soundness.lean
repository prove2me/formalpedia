-- Prove2me | Theorems.Thm_OAI_OptimalMaxCut_LongCode_Game_exists_weighted_soundness
-- name    : OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:53:20.609595+00:00
-- url     : https://prove2.me/theorems/43274bb1-5d2d-44c0-bf8e-3398ab266d0b
-- title:
--   OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness` of [lean/OAI/Computability/MaxCut/Estimates/Dictator.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Dictator.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.OptimalMaxCut.LongCode.Game`, with `open scoped BigOperators`, `open Finset MaxCutGames.Foundations.Hastad`, `open OptimalMaxCut.Unweighted`):
--
--   ```lean
--    theorem exists_weighted_soundness (t : ℚ) (ht : 0 < t) (ht1 : t < 1) (ξ : ℝ) (hξ : 0 < ξ) :
--       ∃ δ : ℝ, 0 < δ ∧ ∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
--         {q N : ℕ} (_hq : 0 < q) (G : Game X Y E q)
--         (enum : X × Cube (Fin q) ≃ Fin N), G.Sound δ →
--         weightedMax (fun u v => (G.weights t ⟨by linarith, ht1.le⟩ enum u v : ℝ)) ≤
--           (1 + 2 / Real.pi * Real.arcsin t) / 2 + ξ
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Foundations.Hastad.Cube` (definitions bundle `OAIQ087A000` of this split); `OAI.OptimalMaxCut.LongCode.Game`, `OAI.OptimalMaxCut.Unweighted.weightedMax` and `OAI.OptimalMaxCut.LongCode.Game.Sound` (definitions bundle `OAIQ087A006` of this split); `OAI.OptimalMaxCut.LongCode.Game.weights` (definitions bundle `OAIQ087A027` of this split).
--
--   **Used by.** The proof of `OAI.OptimalMaxCut.main` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Dictator.lean (declaration OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness)

import Mathlib
import Definitions.Def_OAIQ087A027

section

attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

 theorem exists_weighted_soundness (t : ℚ) (ht : 0 < t) (ht1 : t < 1) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
      {q N : ℕ} (_hq : 0 < q) (G : Game X Y E q)
      (enum : X × Cube (Fin q) ≃ Fin N), G.Sound δ →
      weightedMax (fun u v => (G.weights t ⟨by linarith, ht1.le⟩ enum u v : ℝ)) ≤
        (1 + 2 / Real.pi * Real.arcsin t) / 2 + ξ := by
  sorry

end Game
end OptimalMaxCut.LongCode

end

end OAI
end
