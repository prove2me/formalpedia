-- Prove2me | Theorems.Thm_GlobalTheory_UnitWitt_exists_unitary_mulVec
-- name    : GlobalTheory.UnitWitt.exists_unitary_mulVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:38:56.551772+00:00
-- url     : https://prove2.me/theorems/bc5c3535-3e96-4228-8aee-282120647ba5
-- title:
--   Unit Witt: exists unitary mul Vec
-- statement:
--   The Unit Witt construction uses the exists unitary mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L63-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L63-L79

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitWitt
variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem GlobalTheory.UnitWitt.exists_unitary_mulVec (h2 : (2 : E) ≠ 0) (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v)
    (h0 : star u ⬝ᵥ u ≠ 0) : ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by sorry
