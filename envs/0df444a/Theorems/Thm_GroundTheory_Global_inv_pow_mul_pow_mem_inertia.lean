-- Prove2me | Theorems.Thm_GroundTheory_Global_inv_pow_mul_pow_mem_inertia
-- name    : GroundTheory.Global.inv_pow_mul_pow_mem_inertia
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:34.619964+00:00
-- url     : https://prove2.me/theorems/de7f7286-0856-4774-ac9a-dc3537abb246
-- title:
--   Global: inv pow mul pow mem inertia
-- statement:
--   The Global construction uses the inv pow mul pow mem inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L65-L74

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
variable {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]

theorem GroundTheory.Global.inv_pow_mul_pow_mem_inertia {P : Ideal S} {a b : G} (ha : a ∈ MulAction.stabilizer G P)
    (hab : b * a⁻¹ ∈ P.inertia G) (m : ℕ) : (a ^ m)⁻¹ * b ^ m ∈ P.inertia G := by sorry
