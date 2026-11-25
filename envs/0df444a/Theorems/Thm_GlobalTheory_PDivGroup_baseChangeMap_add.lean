-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_baseChangeMap_add
-- name    : GlobalTheory.PDivGroup.baseChangeMap_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:16.584902+00:00
-- url     : https://prove2.me/theorems/f016daa9-5ced-4026-9014-0170207dc5d6
-- title:
--   PDiv Group: base Change Map add
-- statement:
--   The PDiv Group construction uses the base Change Map add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L493-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L493-L501

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
variable (G H K : PDivGroup p O) (O') [Algebra O O']
variable {G H K}

theorem GlobalTheory.PDivGroup.baseChangeMap_add (f g : G ⟶ H) :
    baseChangeMap O' (f + g) = baseChangeMap O' f + baseChangeMap O' g := by sorry
