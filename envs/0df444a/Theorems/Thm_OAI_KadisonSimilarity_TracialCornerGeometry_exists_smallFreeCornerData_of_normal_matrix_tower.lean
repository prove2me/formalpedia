-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_exists_smallFreeCornerData_of_normal_matrix_tower
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:33:30.066046+00:00
-- url     : https://prove2.me/theorems/a7ce9070-dd90-4043-af0c-10cc57cabead
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/NormalSmallCorners.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/NormalSmallCorners.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`, with `open Generator.Tracial UltrapowerBridge`, `open scoped CStarAlgebra`):
--
--   ```lean
--   theorem exists_smallFreeCornerData_of_normal_matrix_tower
--       (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
--       (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
--       (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
--       {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData G.trace s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.NestedTracialMatrices` and `OAI.KadisonSimilarity.TracialCornerGeometry` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.SmallFreeCornerData` (definitions bundle `OAIQ075A016` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/NormalSmallCorners.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower)

import Mathlib
import Definitions.Def_OAIQ075A016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

include M in
theorem exists_smallFreeCornerData_of_normal_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData G.trace s) := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
