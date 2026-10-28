-- Prove2me | Theorems.Thm_OAI_Thomason_GrayRecursive_IntervalHom_chainComparison_poset_twocells_bijective
-- name    : OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:17:14.035433+00:00
-- url     : https://prove2.me/theorems/c7fedd83-d2a6-4e95-b41a-12184edd1027
-- title:
--   OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective: intermediate lemma from OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective` of [lean/OAI/CategoryTheory/Thomason/Thomason/TwoCellComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/TwoCellComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Thomason.GrayRecursive.IntervalHom`, with `open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory`):
--
--   ```lean
--   theorem chainComparison_poset_twocells_bijective (P : Type u) [PartialOrder P] :
--       Function.Bijective ((chainComparison (NormalizedChains.complex P)).onCells 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Thomason.DirectedComplex.cylinder` and `OAI.Thomason.OmegaCategory.Cells` (definitions bundle `OAIQ043T001` of this split); `OAI.Thomason.OmegaCategory.Functor.onCells` (definitions bundle `OAIQ043T002` of this split); `OAI.Thomason.GrayRecursive.IntervalHom.chainComparison` and `OAI.Thomason.GrayRecursive.IntervalHom.tensorFunctor` (definitions bundle `OAIQ043T012` of this split); `OAI.Thomason.OmegaCategory`, `OAI.Thomason.DirectedComplex.nu`, `OAI.Thomason.NormalizedChains.complex` and `OAI.Thomason.OmegaCategory.instCategory` (the published bundle `Def_ThomasonModelStructures`).
--
--   **Used by.** The proof of `OAI.Thomason.main` of this split imports it.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/TwoCellComparison.lean (declaration OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective)

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u v w z

namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}} {M : DirectedComplex.{u}}

theorem chainComparison_poset_twocells_bijective (P : Type u) [PartialOrder P] :
    Function.Bijective ((chainComparison (NormalizedChains.complex P)).onCells 2) := by
  sorry
end Thomason.GrayRecursive.IntervalHom

end

end OAI
end
