-- Prove2me | Theorems.Thm_KStar_TotallyRealRoots_mem_princ
-- name    : KStar.TotallyRealRoots.mem_princ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:37.467571+00:00
-- url     : https://prove2.me/theorems/6b83d311-aa7a-4963-9185-3341b4362cdb
-- title:
--   Totally Real Roots: mem princ
-- statement:
--   The Totally Real Roots construction uses the mem princ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L49-L52

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

theorem KStar.TotallyRealRoots.mem_princ {a : ℕ} {u : ℤ_[l]ˣ} : u ∈ princ l a ↔ (l : ℤ_[l]) ^ a ∣ (u : ℤ_[l]) - 1 := by sorry
