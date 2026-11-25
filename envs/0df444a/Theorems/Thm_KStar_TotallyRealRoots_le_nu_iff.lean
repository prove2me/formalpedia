-- Prove2me | Theorems.Thm_KStar_TotallyRealRoots_le_nu_iff
-- name    : KStar.TotallyRealRoots.le_nu_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:58.874502+00:00
-- url     : https://prove2.me/theorems/519e8cee-89b6-43fa-af21-805290d3c6c6
-- title:
--   Totally Real Roots: le nu iff
-- statement:
--   The Totally Real Roots construction uses the le nu iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean#L54-L57

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

theorem KStar.TotallyRealRoots.le_nu_iff {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} :
    (n : ℕ∞) ≤ nu l U tr ↔ ∀ u ∈ U, (l : ℤ_[l]) ^ n ∣ (u : ℤ_[l]) ^ tr - 1 := by sorry
