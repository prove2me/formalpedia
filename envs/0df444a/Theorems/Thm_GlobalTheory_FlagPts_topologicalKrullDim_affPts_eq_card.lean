-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_topologicalKrullDim_affPts_eq_card
-- name    : GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:16.502977+00:00
-- url     : https://prove2.me/theorems/0f1d24f0-5792-4038-9b61-18f714f75106
-- title:
--   Flag Pts: topological Krull Dim aff Pts eq card
-- statement:
--   The Flag Pts construction uses the topological Krull Dim aff Pts eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TopologicalKrullDimAffinePoints.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TopologicalKrullDimAffinePoints.lean#L155-L160

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

theorem GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J],
      topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by sorry
