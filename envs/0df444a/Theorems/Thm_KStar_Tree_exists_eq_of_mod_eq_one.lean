-- Prove2me | Theorems.Thm_KStar_Tree_exists_eq_of_mod_eq_one
-- name    : KStar.Tree.exists_eq_of_mod_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:56.816563+00:00
-- url     : https://prove2.me/theorems/f66834b6-a703-4b06-9560-d9d6b75d8a22
-- title:
--   Tree: exists eq of mod eq one
-- statement:
--   The Tree construction uses the exists eq of mod eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/OneAddPow.lean#L37-L41

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

theorem KStar.Tree.exists_eq_of_mod_eq_one {q n : ℕ} (hq : q % (2 * n) = 1) : ∃ c, q = 2 * n * c + 1 := by sorry
