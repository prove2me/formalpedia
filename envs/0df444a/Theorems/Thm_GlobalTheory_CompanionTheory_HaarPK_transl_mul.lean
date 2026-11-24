-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_transl_mul
-- name    : GlobalTheory.CompanionTheory.HaarPK.transl_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:17.93675+00:00
-- url     : https://prove2.me/theorems/96db1c9e-606a-4a64-a6b8-d811647ad2c9
-- title:
--   Haar PK: transl mul
-- statement:
--   The Haar PK construction uses the transl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L76-L82

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

theorem GlobalTheory.CompanionTheory.HaarPK.transl_mul (M : Subgroup G) (η : Measure M) (q x : G) :
    transl M η (q * x) = (transl M η x).map (fun y => q * y) := by sorry
