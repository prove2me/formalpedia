-- Prove2me | Theorems.Thm_GlobalTheory_UpqHaarRight_isMulRightInvariant
-- name    : GlobalTheory.UpqHaarRight.isMulRightInvariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:37:49.375807+00:00
-- url     : https://prove2.me/theorems/831425c6-f578-48a3-b683-9068289b416f
-- title:
--   Upq Haar Right: is Mul Right Invariant
-- statement:
--   The Upq Haar Right construction uses the is Mul Right Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Imports.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Imports.lean#L9-L11

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Imports
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.UpqHaarRight

theorem GlobalTheory.UpqHaarRight.isMulRightInvariant :
    ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by sorry
