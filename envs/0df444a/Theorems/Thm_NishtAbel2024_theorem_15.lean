-- Prove2me | Theorems.Thm_NishtAbel2024_theorem_15
-- name    : NishtAbel2024.theorem_15
-- status  : Disproved
-- author  : @kmehltretter82
-- created : 2026-10-31T19:07:47.330286+00:00
-- url     : https://prove2.me/theorems/5e7c8563-e0a1-46a1-9a0a-b2c0a8e1efc2
-- title:
--   Main Soundness Theorem: Type Safety and Strong Normalization of Algorithm 2 (Theorem 15)
-- statement:
--   Theorem 15 (Section 6.5, p. 59): For any semantically valid global signature `sig` (`SemSigValid sig`) and any unannotated System `F_ω^c` mutual block `Ξ` accepted by Algorithm 2 (`Algorithm2Accepts sig Ξ Ξannot`), the resulting size-annotated mutual block `Ξannot` is well-typed in System `F_ω^{cop, SCT}` (`MutualBlockTyping sig Ξannot`) and semantically valid / strongly normalizing (`SemMutualBlockValid sig Ξannot`).
-- source:
--   Kanstantsin Nisht, 'Type-Based Termination Checking in Agda', Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, 30th International Conference on Types for Proofs and Programs (TYPES 2024). Section 6.5, Theorem 15 (p. 59).

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics
import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

/-- Theorem 15 (Soundness of termination checking, Section 6.5, p. 59):
If `⊨ Σ` (`SemSigValid sig`) and Algorithm 2 accepts a mutually recursive block `Ξ`
(`Algorithm2Accepts sig Ξ Ξannot`), then the size-annotated block `Ξannot` is well-typed in
System `F_ω^{cop, SCT}` (`MutualBlockTyping sig Ξannot`) and is semantically sound / strongly
normalizing (`SemMutualBlockValid sig Ξannot`). -/
theorem theorem_15
    (sig : GlobalSig) (Ξ Ξannot : MutualBlock)
    (hsig : SemSigValid sig)
    (hacc : Algorithm2Accepts sig Ξ Ξannot) :
    MutualBlockTyping sig Ξannot ∧ SemMutualBlockValid sig Ξannot := by
  sorry

end NishtAbel2024
