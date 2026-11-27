-- Prove2me | Theorems.Thm_KStar_TotallyRealRoots_mem_levelGroup
-- name    : KStar.TotallyRealRoots.mem_levelGroup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:56.167882+00:00
-- url     : https://prove2.me/theorems/697b8ed8-22ae-5bcb-8628-e3003ebef471
-- title:
--   Totally Real Roots: mem level Group
-- statement:
--   The Totally Real Roots construction uses the mem level Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L67-L69

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

theorem KStar.TotallyRealRoots.mem_levelGroup {N : ℕ} {H : Subgroup (ZMod N)ˣ} {u : ℤ_[l]ˣ} :
    u ∈ levelGroup l N H ↔
      ∃ h ∈ H, ZMod.unitsMap (Nat.ordProj_dvd N l) h = redPow l (N.factorization l) u := by sorry
