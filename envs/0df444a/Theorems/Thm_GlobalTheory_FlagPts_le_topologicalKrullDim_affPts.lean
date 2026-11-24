-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_le_topologicalKrullDim_affPts
-- name    : GlobalTheory.FlagPts.le_topologicalKrullDim_affPts
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:05.232888+00:00
-- url     : https://prove2.me/theorems/fa58764a-1f79-42fa-8e3e-685ec423ea56
-- title:
--   Flag Pts: le topological Krull Dim aff Pts
-- statement:
--   The Flag Pts construction uses the le topological Krull Dim aff Pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TopologicalKrullDimAffinePoints.lean#L133-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TopologicalKrullDimAffinePoints.lean#L133-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts
open MvPolynomial
variable {k : Type} [Field k] {J : Type}

theorem GlobalTheory.FlagPts.le_topologicalKrullDim_affPts [Infinite k] [Fintype J] :
    ((Fintype.card J : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (AffPts k J) := by sorry
