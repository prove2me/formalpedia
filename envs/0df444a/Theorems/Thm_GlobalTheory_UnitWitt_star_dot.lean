-- Prove2me | Theorems.Thm_GlobalTheory_UnitWitt_star_dot
-- name    : GlobalTheory.UnitWitt.star_dot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:38:44.945202+00:00
-- url     : https://prove2.me/theorems/fc31ba4c-cfc7-406d-b419-2f5e0d7a0d44
-- title:
--   Unit Witt: star dot
-- statement:
--   The Unit Witt construction uses the star dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L48-L49

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

theorem GlobalTheory.UnitWitt.star_dot (x y : Fin r → E) : star (star x ⬝ᵥ y) = star y ⬝ᵥ x := by sorry
