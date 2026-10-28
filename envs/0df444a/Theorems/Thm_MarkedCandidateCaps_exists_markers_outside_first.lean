-- Prove2me | Theorems.Thm_MarkedCandidateCaps_exists_markers_outside_first
-- name    : MarkedCandidateCaps.exists_markers_outside_first
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:02.719858+00:00
-- url     : https://prove2.me/theorems/861aa831-97c2-4527-9d00-5606c01ec224
-- title:
--   Eligible markers can be chosen outside a target set first
-- statement:
--   Let \(T,E\) be finite sets, and let \(m\le|E|\). There is an \(m\)-element subset \(M\subseteq E\) such that
--   \[
--   |T\cap M|\le\max\{0,m-|E\setminus T|\}.
--   \]
--   This gives the exact overlap correction when selecting eligible markers for a target-prefix cap.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, MarkedCandidateCaps, lines 63–102; source SHA256 70f36cf46863ef614a9073ec6c026de5ae5410330d52f60a12e96f629777f587.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace CandidateCoherence
end CandidateCoherence
namespace GuardAugmentation
end GuardAugmentation
namespace ResidualCaps
end ResidualCaps
namespace TournamentHighRows
end TournamentHighRows
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace MarkedCandidateCaps
end MarkedCandidateCaps
open MarkedCandidateCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
variable {V X : Type} [Fintype V] [DecidableEq V]

theorem MarkedCandidateCaps.exists_markers_outside_first (T E : Finset V) (m : ℕ) (hm : m ≤ E.card) :
    ∃ M : Finset V, M ⊆ E ∧ M.card = m ∧ (T ∩ M).card ≤ m - (E \ T).card := by sorry
