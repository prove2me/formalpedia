-- Prove2me | Theorems.Thm_NishtAbel2024V2_theorem_15
-- name    : NishtAbel2024V2.theorem_15
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T21:46:09.069269+00:00
-- url     : https://prove2.me/theorems/ce4466c2-913e-41da-8ad1-cfe140a7b095
-- title:
--   Repaired V2 Main Soundness Theorem: Type Safety and Strong Normalization of Postchecked Algorithm 2 under Scoped Block Extension (Theorem 15)
-- statement:
--   Repaired V2 formulation of Theorem 15 (p. 59) of Nisht & Abel (2024): under a well-scoped block extension `scopeBlockExtension sig Ξannot`, ambient semantic validity `SemSigValidIn sig Ξannot`, and `PostcheckedAlgorithm2Accepts sig Ξ Ξannot`, the size-annotated mutual block `Ξannot` satisfies `MutualBlockTyping sig Ξannot` and `SemMutualBlockValid sig Ξannot`.
--
--   **Differences from the thesis.** The new block must be a well-scoped extension of a closed signature (`scopeBlockExtension`), the existing signature is assumed valid in the world that includes the new block (`SemSigValidIn`), and acceptance by Algorithm 2 includes a final type check of each size-annotated clause (`PostcheckedAlgorithm2Accepts`), so the typing half of the conclusion rests on that check. This statement replaces the refuted `NishtAbel2024.theorem_15`.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Semantics
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2

/-- Repaired Theorem15 (Soundness of termination checking, Section 6.5, p. 59) in `NishtAbel2024V2`:
Under a well-scoped block extension `scopeBlockExtension sig Ξannot`, ambient semantic validity
`SemSigValidIn sig Ξannot`, and postchecked Algorithm 2 acceptance
`PostcheckedAlgorithm2Accepts sig Ξ Ξannot`, the size-annotated block `Ξannot` is well-typed in
System `F_ω^{cop, SCT}` (`MutualBlockTyping sig Ξannot`) and is semantically sound / strongly
normalizing (`SemMutualBlockValid sig Ξannot`). -/
theorem theorem_15
    (sig : GlobalSig) (Ξ Ξannot : MutualBlock)
    (hscope : scopeBlockExtension sig Ξannot)
    (hsig : SemSigValidIn sig Ξannot)
    (hacc : PostcheckedAlgorithm2Accepts sig Ξ Ξannot) :
    MutualBlockTyping sig Ξannot ∧ SemMutualBlockValid sig Ξannot := by
  sorry

end NishtAbel2024V2
