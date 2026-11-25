-- Prove2me | Theorems.Thm_KStar_Tree_exists_sq_unit_not_dvd
-- name    : KStar.Tree.exists_sq_unit_not_dvd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:00.887464+00:00
-- url     : https://prove2.me/theorems/80f05d02-41e6-4ff6-aab0-4d6ad98f7b8c
-- title:
--   Tree: exists sq unit not dvd
-- statement:
--   The Tree construction uses the exists sq unit not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuSumApprox.lean#L88-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuSumApprox.lean#L88-L111

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
variable (l : ℕ) [Fact l.Prime]

theorem KStar.Tree.exists_sq_unit_not_dvd (n : ℕ) (hn : ¬ (l - 1) / 2 ∣ n) (hl : l ≠ 2) :
    ∃ u : ℤ_[l]ˣ, ¬ (l : ℤ_[l]) ^ (0 + 1) ∣ ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by sorry
