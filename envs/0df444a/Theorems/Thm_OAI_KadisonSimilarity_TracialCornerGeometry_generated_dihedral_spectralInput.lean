-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_generated_dihedral_spectralInput
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T09:20:14.685973+00:00
-- url     : https://prove2.me/theorems/59890db7-7190-4a52-9b41-d6526ace8f35
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/NormalFreeDihedral.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/NormalFreeDihedral.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem generated_dihedral_spectralInput
--       (h1 : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)
--       (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
--       (D B : StarSubalgebra ℂ A) (hfree : ScalarFree G.trace D B)
--       (d s : Aˣ) (hd : (d : A) ∈ D) (hs : (s : A) ∈ B)
--       (hd0 : G.trace (d : A) = 0) (hs0 : G.trace (s : A) = 0)
--       (hdi : d⁻¹ = d) (hsi : s⁻¹ = s)
--       (hds : star d = d) (hss : star s = s) :
--       DihedralSpectralArcInput G.trace
--         (G.generatedDihedralAlgebra (d : A) (s : A)) (d * s) d
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.ScalarFree` and `OAI.KadisonSimilarity.TracialCornerGeometry` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.DihedralSpectralArcInput` (definitions bundle `OAIQ075A010` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/NormalFreeDihedral.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput)

import Mathlib
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem generated_dihedral_spectralInput
    (h1 : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (D B : StarSubalgebra ℂ A) (hfree : ScalarFree G.trace D B)
    (d s : Aˣ) (hd : (d : A) ∈ D) (hs : (s : A) ∈ B)
    (hd0 : G.trace (d : A) = 0) (hs0 : G.trace (s : A) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s)
    (hds : star d = d) (hss : star s = s) :
    DihedralSpectralArcInput G.trace
      (G.generatedDihedralAlgebra (d : A) (s : A)) (d * s) d := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
