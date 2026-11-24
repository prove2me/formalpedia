-- Prove2me | Theorems.Thm_GlobalTheory_UnitWitt_refl_mulVec
-- name    : GlobalTheory.UnitWitt.refl_mulVec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:38:43.455788+00:00
-- url     : https://prove2.me/theorems/cd4cb3f5-3f75-4e06-a9c2-160d499fe301
-- title:
--   Unit Witt: refl mul Vec
-- statement:
--   The Unit Witt construction uses the refl mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L42-L46

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

theorem GlobalTheory.UnitWitt.refl_mulVec (w u : Fin r → E) (a : E) (ha : star w ⬝ᵥ u = a) (ha0 : a ≠ 0) :
    (1 - a⁻¹ • vecMulVec w (star w)) *ᵥ u = u - w := by sorry
