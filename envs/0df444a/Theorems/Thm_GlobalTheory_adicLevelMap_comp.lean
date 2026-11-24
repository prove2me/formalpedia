-- Prove2me | Theorems.Thm_GlobalTheory_adicLevelMap_comp
-- name    : GlobalTheory.adicLevelMap_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:00.733365+00:00
-- url     : https://prove2.me/theorems/96e62002-b095-484b-8b96-757bc35cacb0
-- title:
--   Global Theory: adic Level Map comp
-- statement:
--   The Global Theory construction uses the adic Level Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L197-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L197-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)

theorem GlobalTheory.adicLevelMap_comp {l m n : ℕ} (h : l ≤ m) (h' : m ≤ n) :
    adicLevelMap I h ≫ adicLevelMap I h' = adicLevelMap I (h.trans h') := by sorry
