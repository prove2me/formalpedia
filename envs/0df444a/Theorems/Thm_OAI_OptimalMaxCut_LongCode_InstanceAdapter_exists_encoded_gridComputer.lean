-- Prove2me | Theorems.Thm_OAI_OptimalMaxCut_LongCode_InstanceAdapter_exists_encoded_gridComputer
-- name    : OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T18:02:17.887582+00:00
-- url     : https://prove2.me/theorems/53328080-a8b8-4a25-91b9-ff1157e0a364
-- title:
--   OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer` of [lean/OAI/Computability/MaxCut/Main.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Main.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.OptimalMaxCut.LongCode.InstanceAdapter`, with `open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity`):
--
--   ```lean
--    theorem exists_encoded_gridComputer (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
--       ∃ pc : Turing.TM2ComputableInPolyTime (gameBits : Instance q → List Bool) ScaledGraph.bits
--         (fun g => gridGraph g t ht K), MachineFiniteAlphabet.FiniteAlphabet pc.tm
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Foundations.Target.Instance` and `OAI.MaxCutGames.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet` (definitions bundle `OAIQ087A001` of this split); `OAI.MaxCutGames.Foundations.Complexity.gameBits` (definitions bundle `OAIQ087A009` of this split); `OAI.OptimalMaxCut.LongCode.InstanceAdapter.gridGraph` (definitions bundle `OAIQ087A032` of this split); `OAI.OptimalMaxCut.ScaledGraph` and `OAI.OptimalMaxCut.ScaledGraph.bits` (the published bundle `Def_OptimalMaxCut`).
--
--   **Used by.** The proof of `OAI.OptimalMaxCut.main` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Main.lean (declaration OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer)

import Mathlib
import Definitions.Def_OptimalMaxCut
import Definitions.Def_OAIQ087A032

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace OptimalMaxCut.LongCode.InstanceAdapter
open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

 theorem exists_encoded_gridComputer (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    ∃ pc : Turing.TM2ComputableInPolyTime (gameBits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K), MachineFiniteAlphabet.FiniteAlphabet pc.tm := by
  sorry
end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
end
