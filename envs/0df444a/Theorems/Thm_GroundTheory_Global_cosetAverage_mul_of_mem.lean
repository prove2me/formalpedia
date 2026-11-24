-- Prove2me | Theorems.Thm_GroundTheory_Global_cosetAverage_mul_of_mem
-- name    : GroundTheory.Global.cosetAverage_mul_of_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:42.532955+00:00
-- url     : https://prove2.me/theorems/dc63a375-0445-4db9-986b-f66182ccd7f8
-- title:
--   Global: coset Average mul of mem
-- statement:
--   The Global construction uses the coset Average mul of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L19-L24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
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
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G : Type*} [Group G]

theorem GroundTheory.Global.cosetAverage_mul_of_mem (I : Subgroup G) (f : G → ℂ) (g : G) {j : G} (hj : j ∈ I) :
    cosetAverage I f (g * j) = cosetAverage I f g := by sorry
