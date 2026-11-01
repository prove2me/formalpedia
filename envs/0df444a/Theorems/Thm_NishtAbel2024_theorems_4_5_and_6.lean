-- Prove2me | Theorems.Thm_NishtAbel2024_theorems_4_5_and_6
-- name    : NishtAbel2024.theorems_4_5_and_6
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T19:04:50.632731+00:00
-- url     : https://prove2.me/theorems/4d0bacd0-9075-4d78-861e-8737ecb6bdcd
-- title:
--   Strong Normalization of Mutual Blocks & Programs (Theorems 4 & 5), and Embedding of System F_ω^{cop} (Theorem 6)
-- statement:
--   Theorems 4, 5, and 6 (Sections 5.4.4–5.5, pp. 37–40): (1) every well-typed mutual block `MutualBlockTyping sig Ξ` over a semantically valid signature `sig` is semantically valid and strongly normalizing (`SemMutualBlockValid sig Ξ`); (2) every well-typed signature sequence `SigBlocksTyping` is semantically valid; (3) every well-typed program `ProgramTyping P` is strongly normalizing (`SemProgramValid P`); and (4) every System `F_ω^{cop}` mutual block with a lexicographic size measure embeds into System `F_ω^{cop, SCT}` (`MutualBlockTyping`).
-- source:
--   Kanstantsin Nisht, 'Type-Based Termination Checking in Agda', Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, 30th International Conference on Types for Proofs and Programs (TYPES 2024). Sections 5.4.4–5.5, Theorem 4 (p. 37), Theorem 5 (p. 38), and Theorem 6 (p. 39).

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics

namespace NishtAbel2024

/-- Theorem 4 (Soundness of mutual blocks, p. 37), Lemma 2 (Soundness of global environment, p. 38),
Theorem 5 (Soundness of programs in System `F_ω^{cop, SCT}`, p. 38), and
Theorem 6 (Relation of System `F_ω^{cop, SCT}` and System `F_ω^{cop}`, p. 39):
1. (**Theorem 4**) If `⊨ Σ` and `Σ ⊢ Ξ`, then `Σ ⊨ Ξ`.
2. (**Lemma 2**) If `⊢ Σ`, then `⊨ Σ`.
3. (**Theorem 5**) If `⊢ P`, then `⊨ P` (`P.main ∈ SN`).
4. (**Theorem 6**) If `Σ ⊢ Ξ` in System `F_ω^{cop}`, then `Σ ⊢ |Ξ|` in System `F_ω^{cop, SCT}`. -/
theorem theorems_4_5_and_6 :
    (∀ (sig : GlobalSig) (Ξ : MutualBlock),
      SemSigValid sig →
      MutualBlockTyping sig Ξ →
      SemMutualBlockValid sig Ξ) ∧
    (∀ blocks : List MutualBlock,
      SigBlocksTyping blocks →
      SemSigValid blocks.flatten) ∧
    (∀ P : Program,
      ProgramTyping P →
      SemProgramValid P) ∧
    (∀ (sig : GlobalSig) (Ξcop : List CopFunDecl),
      CopMutualBlockTyping sig Ξcop →
      MutualBlockTyping sig (eraseMeasures Ξcop)) := by
  sorry

end NishtAbel2024
