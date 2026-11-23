-- Prove2me | Theorems.Thm_KStar_Tree_pow_nuOf_dvd
-- name    : KStar.Tree.pow_nuOf_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:56.65189+00:00
-- url     : https://prove2.me/theorems/ca9a5463-3451-43b1-8098-97034b0d5d0b
-- title:
--   Tree: pow nu Of dvd
-- statement:
--   The Tree construction uses the pow nu Of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuBasic.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuBasic.lean#L36-L46

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

theorem KStar.Tree.pow_nuOf_dvd (g : Γ) : (l : ℤ_[l]) ^ nuOf l ε n ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by sorry
