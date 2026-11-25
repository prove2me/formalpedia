-- Prove2me | Theorems.Thm_GlobalTheory_weierstrassP_add_sub_weierstrassP_sub
-- name    : GlobalTheory.weierstrassP_add_sub_weierstrassP_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:24.330494+00:00
-- url     : https://prove2.me/theorems/b7cf17a2-9fe7-4996-961d-26e65d4c02cf
-- title:
--   Global Theory: weierstrass P add sub weierstrass P sub
-- statement:
--   The Global Theory construction uses the weierstrass P add sub weierstrass P sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassPAddSubWeierstrassPSub.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassPAddSubWeierstrassPSub.lean#L6-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassPAddSubWeierstrassPSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.weierstrassP_add_sub_weierstrassP_sub (L : PeriodPair) (z w : ℂ) (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h₁ : z - w ∉ L.lattice) (h₂ : z + w ∉ L.lattice) :
    (L.weierstrassP z - L.weierstrassP w) ^ 2 *
        (L.weierstrassP (z + w) - L.weierstrassP (z - w)) =
      -(L.derivWeierstrassP z * L.derivWeierstrassP w) := by sorry
