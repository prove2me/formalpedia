-- Prove2me | Theorems.Thm_KStar_Tree_exists_unit_not_dvd
-- name    : KStar.Tree.exists_unit_not_dvd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:54.240327+00:00
-- url     : https://prove2.me/theorems/0601f60f-4918-4393-9568-8a4f12c6c09b
-- title:
--   Tree: exists unit not dvd
-- statement:
--   The Tree construction uses the exists unit not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuSumApprox.lean#L62-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuSumApprox.lean#L62-L86

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

theorem KStar.Tree.exists_unit_not_dvd (C n : ℕ) (hC : C ≠ 0) (h2 : 2 ∣ C) (hn : Odd n) :
    ∃ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ C.factorization l ∣ (u : ℤ_[l]) - 1 ∧
      ¬ (l : ℤ_[l]) ^ (C.factorization l + (if l ∣ C then n.factorization l else 0) + 1) ∣ (u : ℤ_[l]) ^ n - 1 := by sorry
