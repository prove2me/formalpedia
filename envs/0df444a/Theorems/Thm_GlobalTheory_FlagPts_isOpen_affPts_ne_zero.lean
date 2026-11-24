-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_isOpen_affPts_ne_zero
-- name    : GlobalTheory.FlagPts.isOpen_affPts_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:59.176801+00:00
-- url     : https://prove2.me/theorems/33a6aa64-2ea7-44ac-8228-29d01c4fd0f0
-- title:
--   Flag Pts: is Open aff Pts ne zero
-- statement:
--   The Flag Pts construction uses the is Open aff Pts ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UniMatBlockTriangular.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UniMatBlockTriangular.lean#L19-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts

theorem GlobalTheory.FlagPts.isOpen_affPts_ne_zero {k J : Type} [Field k] (p : MvPolynomial J k) :
    IsOpen {x : AffPts k J | MvPolynomial.eval x p ≠ 0} := by sorry
