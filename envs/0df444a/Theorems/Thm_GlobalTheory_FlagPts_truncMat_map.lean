-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_truncMat_map
-- name    : GlobalTheory.FlagPts.truncMat_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:06.892818+00:00
-- url     : https://prove2.me/theorems/011d76db-f461-46a3-a764-083f638ee665
-- title:
--   Flag Pts: trunc Mat map
-- statement:
--   The Flag Pts construction uses the trunc Mat map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TruncMatMemSubalgebra.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TruncMatMemSubalgebra.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TruncMatMemSubalgebra
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

theorem GlobalTheory.FlagPts.truncMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (m : ℕ)
    (M : Matrix (Fin d) (Fin d) R) : (truncMat m M).map f = truncMat m (M.map f) := by sorry
