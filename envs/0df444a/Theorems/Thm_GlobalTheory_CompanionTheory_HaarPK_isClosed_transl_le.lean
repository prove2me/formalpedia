-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_isClosed_transl_le
-- name    : GlobalTheory.CompanionTheory.HaarPK.isClosed_transl_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:35.900898+00:00
-- url     : https://prove2.me/theorems/16aafb41-dcc4-446d-be8d-007c9546e400
-- title:
--   Haar PK: is Closed transl le
-- statement:
--   The Haar PK construction uses the is Closed transl le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L84-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L84-L100

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.CompanionTheory.HaarPK.isClosed_transl_le (M : Subgroup G) (η : Measure M) [η.Regular] {U : Set G} (hU : IsOpen U) (t : ℝ≥0∞) :
    IsClosed {x | transl M η x U ≤ t} := by sorry
