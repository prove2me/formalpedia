-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_measurable_transl_fun
-- name    : GlobalTheory.CompanionTheory.HaarPK.measurable_transl_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:37.641349+00:00
-- url     : https://prove2.me/theorems/d27bf190-f870-4a25-9747-be4fa0c59b9d
-- title:
--   Haar PK: measurable transl fun
-- statement:
--   The Haar PK construction uses the measurable transl fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L64-L65

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

theorem GlobalTheory.CompanionTheory.HaarPK.measurable_transl_fun (M : Subgroup G) (x : G) : Measurable (fun m : M => x * (m : G)) := by sorry
