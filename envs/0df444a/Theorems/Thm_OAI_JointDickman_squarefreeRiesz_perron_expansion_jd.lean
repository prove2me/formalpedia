-- Prove2me | Theorems.Thm_OAI_JointDickman_squarefreeRiesz_perron_expansion_jd
-- name    : OAI.JointDickman.squarefreeRiesz_perron_expansion_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:35:06.163117+00:00
-- url     : https://prove2.me/theorems/5e27477e-52fc-4e92-8487-875c3e83e1fe
-- title:
--   OAI.JointDickman.squarefreeRiesz_perron_expansion_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.squarefreeRiesz_perron_expansion` of [lean/OAI/NumberTheory/JointDickman/Analysis/SquarefreeRieszPerronExpansion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/SquarefreeRieszPerronExpansion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Complex Filter Asymptotics Finset`, `open scoped Topology`):
--
--   ```lean
--   theorem squarefreeRiesz_perron_expansion_jd {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
--       ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z/2 ∧ 0 < c 0 ∧
--         ∀ H : ℕ, (fun L : ℝ =>
--           (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
--           ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.squarefreeLeadingConstant` (definitions bundle `OAIQ083J001` of this split); `VerticalIntegral'` (definitions bundle `OAIQ083J002` of this split); `OAI.JointDickman.squarefreeNormalizedPerron` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.jointDickmanLaw_unconditional_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/SquarefreeRieszPerronExpansion.lean (declaration OAI.JointDickman.squarefreeRiesz_perron_expansion)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Complex Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRiesz_perron_expansion_jd {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z/2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun L : ℝ =>
        (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  sorry

end JointDickman

end OAI
end
