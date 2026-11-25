-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_rigOfOmega_injective
-- name    : GlobalTheory.PDivGroup.rigOfOmega_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:02:19.683162+00:00
-- url     : https://prove2.me/theorems/1487a197-b514-4c44-b69e-9211fa091ac6
-- title:
--   PDiv Group: rig Of Omega injective
-- statement:
--   The PDiv Group construction uses the rig Of Omega injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L177-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L177-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)

theorem GlobalTheory.PDivGroup.rigOfOmega_injective [IsDomain O] (hp : (p : O) ≠ 0) :
    Function.Injective G.rigOfOmega := by sorry
