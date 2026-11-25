-- Prove2me | Theorems.Thm_GroundTheory_Global_cosetAverage_conj
-- name    : GroundTheory.Global.cosetAverage_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:52.120232+00:00
-- url     : https://prove2.me/theorems/e0cd99d5-f5d0-45f3-8d12-26dd928133ff
-- title:
--   Global: coset Average conj
-- statement:
--   The Global construction uses the coset Average conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L26-L40

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

theorem GroundTheory.Global.cosetAverage_conj (I J : Subgroup G) (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) (hIJ : ∀ σ, σ ∈ J ↔ h⁻¹ * σ * h ∈ I) (g : G) :
    cosetAverage J f (h * g * h⁻¹) = cosetAverage I f g := by sorry
