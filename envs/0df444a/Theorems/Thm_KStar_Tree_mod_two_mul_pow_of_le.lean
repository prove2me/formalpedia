-- Prove2me | Theorems.Thm_KStar_Tree_mod_two_mul_pow_of_le
-- name    : KStar.Tree.mod_two_mul_pow_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:56.727888+00:00
-- url     : https://prove2.me/theorems/e81ead5a-078e-4760-b9b3-9fb0a9980ffa
-- title:
--   Tree: mod two mul pow of le
-- statement:
--   The Tree construction uses the mod two mul pow of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L50-L56

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

theorem KStar.Tree.mod_two_mul_pow_of_le {q l k M : ℕ} (hl : l.Prime) (hk : k ≤ M) (hq : q % (2 * l ^ M) = 1) :
    q % (2 * l ^ k) = 1 := by sorry
