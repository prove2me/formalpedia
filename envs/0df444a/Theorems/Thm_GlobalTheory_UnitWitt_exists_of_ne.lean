-- Prove2me | Theorems.Thm_GlobalTheory_UnitWitt_exists_of_ne
-- name    : GlobalTheory.UnitWitt.exists_of_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:13.137187+00:00
-- url     : https://prove2.me/theorems/bdf945ad-324a-4fd5-989b-51e692283c22
-- title:
--   Unit Witt: exists of ne
-- statement:
--   The Unit Witt construction uses the exists of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L51-L61

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

theorem GlobalTheory.UnitWitt.exists_of_ne (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v) (ha : star (u - v) ⬝ᵥ u ≠ 0) :
    ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by sorry
