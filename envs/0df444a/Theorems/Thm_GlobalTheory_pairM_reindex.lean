-- Prove2me | Theorems.Thm_GlobalTheory_pairM_reindex
-- name    : GlobalTheory.pairM_reindex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:08.192969+00:00
-- url     : https://prove2.me/theorems/45e59575-b0bc-4380-841b-cd6f3247026e
-- title:
--   Global Theory: pair M reindex
-- statement:
--   The Global Theory construction uses the pair M reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesFin.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesFin.lean#L31-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix
open GlobalTheory

theorem GlobalTheory.pairM_reindex {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a]
    (e : b ≃ a) (J : Matrix (Fin n) (Fin n) E) (X X' : Matrix (Fin n) a E) :
    pairM σ J (X'.submatrix id e) (X.submatrix id e) = (pairM σ J X' X).submatrix e e := by sorry
