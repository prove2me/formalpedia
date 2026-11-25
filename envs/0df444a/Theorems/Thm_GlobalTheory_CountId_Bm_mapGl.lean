-- Prove2me | Theorems.Thm_GlobalTheory_CountId_Bm_mapGl
-- name    : GlobalTheory.CountId.Bm_mapGl
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:59.521906+00:00
-- url     : https://prove2.me/theorems/7cdd7830-a099-4a3d-b5ee-89e1343e9590
-- title:
--   Count Id: Bm map Gl
-- statement:
--   The Count Id construction uses the Bm map Gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L65-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']

theorem GlobalTheory.CountId.Bm_mapGl (φ : k →+* k') (Y : Gl r k) : Bm (mapGl φ Y) = (Bm Y).map φ := by sorry
