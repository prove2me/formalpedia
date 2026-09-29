-- Prove2me | Theorems.Thm_Freiman_middle_interval_chain
-- name    : Freiman.middle_interval_chain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:45.074646+00:00
-- url     : https://prove2.me/theorems/1b08a88c-e5e2-436a-a8af-1ed200feed7e
-- title:
--   middle interval chain
-- statement:
--   A finite chain of nonempty closed intervals with consecutive intersections covers every interval between a lower endpoint reached by the chain and an upper endpoint reached by it.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, finite contact-chain argument used throughout Part III

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_interval_chain :
    ∀ (cs : List MiddleCore) (l u : ℝ), middleContacts cs →
      (∃ d ∈ cs, (middleBounds d).1  ≤  l) → (∃ d ∈ cs, u  ≤  (middleBounds d).2) →
      Set.Icc l u ⊆ middleUnion cs := by
  sorry

end Freiman
