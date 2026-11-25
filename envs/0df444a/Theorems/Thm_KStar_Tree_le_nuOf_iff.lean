-- Prove2me | Theorems.Thm_KStar_Tree_le_nuOf_iff
-- name    : KStar.Tree.le_nuOf_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:54.415132+00:00
-- url     : https://prove2.me/theorems/c81de8f5-81f9-486f-a4e2-ad0a77497d9a
-- title:
--   Tree: le nu Of iff
-- statement:
--   The Tree construction uses the le nu Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuBasic.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuBasic.lean#L58-L67

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)

theorem KStar.Tree.le_nuOf_iff (h : ∃ g, ε g ^ n ≠ 1) (k : ℕ) :
    k ≤ nuOf l ε n ↔ ∀ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by sorry
