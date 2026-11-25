-- Prove2me | Theorems.Thm_GlobalTheory_weierstrassP_two_mul_mul_sq
-- name    : GlobalTheory.weierstrassP_two_mul_mul_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:49.409466+00:00
-- url     : https://prove2.me/theorems/0892e0e1-e7c1-4fce-9b75-116210c5765a
-- title:
--   Global Theory: weierstrass P two mul mul sq
-- statement:
--   The Global Theory construction uses the weierstrass P two mul mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassPTwoMulMulSq.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassPTwoMulMulSq.lean#L8-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassPTwoMulMulSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PeriodPair WeierstrassCurve
open GlobalTheory

theorem GlobalTheory.weierstrassP_two_mul_mul_sq (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice)
    (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 =
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 -
        2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by sorry
