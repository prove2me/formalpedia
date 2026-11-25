-- Prove2me | Theorems.Thm_KStar_Tree_dvd_choose_two
-- name    : KStar.Tree.dvd_choose_two
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:45.578125+00:00
-- url     : https://prove2.me/theorems/9572b61d-c4df-4f2a-a748-a5397d98dced
-- title:
--   Tree: dvd choose two
-- statement:
--   The Tree construction uses the dvd choose two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L43-L48

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

theorem KStar.Tree.dvd_choose_two {q n : ℕ} (hq : q % (2 * n) = 1) : n ∣ q.choose 2 := by sorry
