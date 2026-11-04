-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_norm_tracialSmallColumn
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.norm_tracialSmallColumn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:18:45.926066+00:00
-- url     : https://prove2.me/theorems/536e6ab0-9cc0-4180-895d-8faf63eb6308
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.norm_tracialSmallColumn: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.norm_tracialSmallColumn` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialSmallColumn.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialSmallColumn.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem norm_tracialSmallColumn (D : StarSubalgebra ℂ P)
--       (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
--       (q : P) (hq : IsStarProjection q) (hqD : q ∈ D)
--       {a : ℝ} (ha : 0 ≤ a) (htrace : G.trace q = (a : ℂ)) (v : G.baseSpace A) :
--       ‖G.tracialSmallColumn A q v‖ = Real.sqrt a * ‖v‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.ScalarFree` and `OAI.KadisonSimilarity.TracialCornerGeometry` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn` (definitions bundle `OAIQ075A023` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialSmallColumn.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.norm_tracialSmallColumn)

import Mathlib
import Definitions.Def_OAIQ075A023

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

theorem norm_tracialSmallColumn (D : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (q : P) (hq : IsStarProjection q) (hqD : q ∈ D)
    {a : ℝ} (ha : 0 ≤ a) (htrace : G.trace q = (a : ℂ)) (v : G.baseSpace A) :
    ‖G.tracialSmallColumn A q v‖ = Real.sqrt a * ‖v‖ := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
