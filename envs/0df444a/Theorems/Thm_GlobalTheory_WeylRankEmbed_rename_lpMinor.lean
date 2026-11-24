-- Prove2me | Theorems.Thm_GlobalTheory_WeylRankEmbed_rename_lpMinor
-- name    : GlobalTheory.WeylRankEmbed.rename_lpMinor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:29.290969+00:00
-- url     : https://prove2.me/theorems/faf0efa5-f23d-439a-a59a-805c2fc424f9
-- title:
--   Weyl Rank Embed: rename lp Minor
-- statement:
--   The Weyl Rank Embed construction uses the rename lp Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RenameUpperLeftCornerMemWeylLattice.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RenameUpperLeftCornerMemWeylLattice.lean#L17-L23

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_RenameUpperLeftCornerMemWeylLattice
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open GlobalTheory
open GlobalTheory.WeylRankEmbed
variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)

theorem GlobalTheory.WeylRankEmbed.rename_lpMinor (s : ℕ) (h1 : s ≤ a) (h2 : s ≤ b) :
    rename (corner hab) (lpMinor R s h1 h1) = lpMinor R s h2 h2 := by sorry
