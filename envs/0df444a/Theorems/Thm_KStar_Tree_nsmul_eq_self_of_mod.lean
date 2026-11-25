-- Prove2me | Theorems.Thm_KStar_Tree_nsmul_eq_self_of_mod
-- name    : KStar.Tree.nsmul_eq_self_of_mod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:41.854458+00:00
-- url     : https://prove2.me/theorems/58dc2032-69a8-49bd-830a-0957248954f2
-- title:
--   Tree: nsmul eq self of mod
-- statement:
--   The Tree construction uses the nsmul eq self of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L58-L61

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_OneAddPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree

theorem KStar.Tree.nsmul_eq_self_of_mod {W : Type} [AddCommGroup W] {q n : ℕ} (hq : q % (2 * n) = 1) (h : ∀ m : W, n • m = 0)
    (m : W) : q • m = m := by sorry
