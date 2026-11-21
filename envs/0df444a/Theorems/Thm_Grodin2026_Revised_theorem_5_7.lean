-- Prove2me | Theorems.Thm_Grodin2026_Revised_theorem_5_7
-- name    : Grodin2026.Revised.theorem_5_7
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T19:14:07.03336+00:00
-- url     : https://prove2.me/theorems/dada6aca-1e64-4d4c-95e3-48f1dd01ddb4
-- title:
--   Theorem 5.7 — Equivalence of the Calf and potential interpretations
-- statement:
--   Let $A$ be any positive AARA type. Its compositional Calf interpretation is isomorphic to $\mathsf{Potential}(\Phi_A : \llbracket A\rrbracket \to \mathbb N)$, where $\Phi_A$ is the potential function in Figure 2.
-- source:
--   Grodin, Chu, Li, Hoffmann, and Harper (2026), Potential Functions as Types, §5.2, Theorem 5.7. https://arxiv.org/html/2607.08547v2#S5.SS2

import Definitions.Def_Grodin2026_AARATypes

namespace Grodin2026.Revised

/-- Theorem 5.7 of Grodin et al. For every positive AARA type, its compositional Calf
interpretation is equivalent to the potential type built from the value set and Figure 2
potential function. -/
theorem theorem_5_7 (A : AARAType) :
    Nonempty (CompEquiv (interpPositiveAARA A)
      (PotentialType (aaraValues A) (aaraPotential A))) := by
  sorry

end Grodin2026.Revised
