-- Prove2me | Theorems.Thm_NishtAbel2024V2_theorems_4_5_and_6
-- name    : NishtAbel2024V2.theorems_4_5_and_6
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T21:45:55.889403+00:00
-- url     : https://prove2.me/theorems/ff97976f-4185-4eda-a37f-ec661059abd1
-- title:
--   Repaired V2 Strong Normalization of Scoped Mutual Blocks & Programs (Theorems 4 & 5) and Embedding of System F_ω^{cop} (Theorem 6)
-- statement:
--   Repaired V2 formulation of Theorem 4 (p. 37), Lemma 2 (p. 38), Theorem 5 (p. 38), and Theorem 6 (p. 39) of Nisht & Abel (2024): incorporates `scopeBlockExtension`, `SemSigValidIn`, `scopeOrderedBlocks`, `ScopedProgramTyping`, and non-empty lexicographic measure hygiene (`measureIndices ≠ []`) in `CopMutualBlockTyping`.
--
--   **Differences from the thesis.** Theorem 4 assumes a well-scoped block extension and validity of the existing signature in the world that includes the block (`scopeBlockExtension`, `SemSigValidIn`). Lemma 2 and Theorem 5 assume blocks ordered without forward references (`scopeOrderedBlocks`, `ScopedProgramTyping`). Theorem 6 requires a non-empty lexicographic measure. This statement replaces the refuted `NishtAbel2024.theorems_4_5_and_6`.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Semantics
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2

/-- Repaired Theorem4 (Soundness of mutual blocks, p. 37), Lemma 2 (Soundness of global environment, p. 38),
Theorem 5 (Soundness of programs in System `F_ω^{cop, SCT}`, p. 38), and
Theorem 6 (Relation of System `F_ω^{cop, SCT}` and System `F_ω^{cop}`, p. 39) in `NishtAbel2024V2`:
1. (**Theorem 4**) Under `scopeBlockExtension sig Ξ` and `SemSigValidIn sig Ξ`, if `Σ ⊢ Ξ`, then `Σ ⊨ Ξ`.
2. (**Lemma 2**) Under `scopeOrderedBlocks blocks`, if `⊢ Σ`, then `⊨ Σ`.
3. (**Theorem 5**) If `ScopedProgramTyping P`, then `⊨ P` (`P.main ∈ SN`).
4. (**Theorem 6**) If `Σ ⊢ Ξ` in System `F_ω^{cop}` (with non-empty lexicographic measure), then
   `Σ ⊢ |Ξ|` in System `F_ω^{cop, SCT}`. -/
theorem theorems_4_5_and_6 :
    (∀ (sig : GlobalSig) (Ξ : MutualBlock),
      scopeBlockExtension sig Ξ →
      SemSigValidIn sig Ξ →
      MutualBlockTyping sig Ξ →
      SemMutualBlockValid sig Ξ) ∧
    (∀ blocks : List MutualBlock,
      scopeOrderedBlocks blocks →
      SigBlocksTyping blocks →
      SemSigValid blocks.flatten) ∧
    (∀ P : Program,
      ScopedProgramTyping P →
      SemProgramValid P) ∧
    (∀ (sig : GlobalSig) (Ξcop : List CopFunDecl),
      CopMutualBlockTyping sig Ξcop →
      MutualBlockTyping sig (eraseMeasures Ξcop)) := by
  sorry

end NishtAbel2024V2
