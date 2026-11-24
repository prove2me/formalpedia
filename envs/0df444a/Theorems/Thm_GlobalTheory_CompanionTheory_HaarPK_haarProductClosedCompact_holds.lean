-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_haarProductClosedCompact_holds
-- name    : GlobalTheory.CompanionTheory.HaarPK.haarProductClosedCompact_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:20.459542+00:00
-- url     : https://prove2.me/theorems/e7395b0b-dde5-4391-809e-19f902bb15ac
-- title:
--   Haar PK: haar Product Closed Compact holds
-- statement:
--   The Haar PK construction uses the haar Product Closed Compact holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L239-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L239-L266

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

theorem GlobalTheory.CompanionTheory.HaarPK.haarProductClosedCompact_holds : Formalism.D.haarProductClosedCompact := by sorry
