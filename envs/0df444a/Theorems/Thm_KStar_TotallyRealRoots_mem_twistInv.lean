-- Prove2me | Theorems.Thm_KStar_TotallyRealRoots_mem_twistInv
-- name    : KStar.TotallyRealRoots.mem_twistInv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:50.060503+00:00
-- url     : https://prove2.me/theorems/f6550f6b-3083-5de5-a99c-3d6a2940a9b4
-- title:
--   Totally Real Roots: mem twist Inv
-- statement:
--   The Totally Real Roots construction uses the mem twist Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L64-L65

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.TotallyRealRoots
variable (l : ℕ) [Fact l.Prime]
variable {l}

theorem KStar.TotallyRealRoots.mem_twistInv {A : Type*} [AddCommGroup A] [Module ℤ_[l] A] {U : Subgroup ℤ_[l]ˣ} {tr : ℕ}
    {x : A} : x ∈ twistInv l A U tr ↔ ∀ u ∈ U, ((u : ℤ_[l]) ^ tr) • x = x := by sorry
