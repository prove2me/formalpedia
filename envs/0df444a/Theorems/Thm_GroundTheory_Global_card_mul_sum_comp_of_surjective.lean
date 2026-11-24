-- Prove2me | Theorems.Thm_GroundTheory_Global_card_mul_sum_comp_of_surjective
-- name    : GroundTheory.Global.card_mul_sum_comp_of_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:17.540773+00:00
-- url     : https://prove2.me/theorems/f90222ef-fe77-4f62-a182-5c9ae45f388a
-- title:
--   Global: card mul sum comp of surjective
-- statement:
--   The Global construction uses the card mul sum comp of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L15-L31

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G H : Type*} [Group G] [Group H]

theorem GroundTheory.Global.card_mul_sum_comp_of_surjective {A B : Type*} [Group A] [Group B] [Fintype A]
    [Fintype B] (ψ : A →* B) (hψ : Function.Surjective ψ) (F : B → ℂ) :
    (Fintype.card B : ℂ) * ∑ a, F (ψ a) = (Fintype.card A : ℂ) * ∑ b, F b := by sorry
