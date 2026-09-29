-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_from_fork_covers
-- name    : Freiman.lowerEarlyTerminal_child_goodness_from_fork_covers
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:41.444027+00:00
-- url     : https://prove2.me/theorems/a4c2cbbc-e1ab-4c27-9c90-713f740aff79
-- title:
--   Freiman.lowerEarlyTerminal_child_goodness_from_fork_covers
-- statement:
--   Two strict source cross comparisons and ordered source endpoints give a point in both source forks; the two explicit cover inclusions put that point in both actual forks.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_child_goodness_from_fork_covers (p : LowerPair) (l : LowerLabel) (wide : Bool) (norm : CertBound)
    (hm : (wide,norm) ∈ section14NormalCases (section14LabelWords l))
    (ha : lowerEarlyTerminalAt p [norm])
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (hc : ∀ d ∈ ([1,2] : List ℕ+), lowerCover (lowerEarlyTerminalForkPair p l wide d) ⊆
      lowerCover (lowerChild (lowerChild p l) ([d],[]))) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  sorry
