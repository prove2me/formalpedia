-- Prove2me | Theorems.Thm_KStar_Tree_nuOf_pos_of_res
-- name    : KStar.Tree.nuOf_pos_of_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:57.069459+00:00
-- url     : https://prove2.me/theorems/0c41cc04-e488-4347-83d9-247daf1544e7
-- title:
--   Tree: nu Of pos of res
-- statement:
--   The Tree construction uses the nu Of pos of res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuBasic.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuBasic.lean#L69-L76

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

theorem KStar.Tree.nuOf_pos_of_res (h : ∃ g, ε g ^ n ≠ 1) {K : Type} [CommRing K] [Nontrivial K] (θ : ℤ_[l] →+* K)
    (h1 : ∀ g, θ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1) : 0 < nuOf l ε n := by sorry
