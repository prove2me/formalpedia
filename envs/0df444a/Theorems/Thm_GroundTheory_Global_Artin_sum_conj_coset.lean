-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_sum_conj_coset
-- name    : GroundTheory.Global.Artin.sum_conj_coset
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:31.269186+00:00
-- url     : https://prove2.me/theorems/4ec0e15f-2b19-417a-b4f4-8266c9e4af6c
-- title:
--   Artin: sum conj coset
-- statement:
--   The Artin construction uses the sum conj coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L139-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L139-L155

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
variable {H D I : Subgroup G}

theorem GroundTheory.Global.Artin.sum_conj_coset [Fintype I] (hID : I ≤ D) [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (F : G → ℂ) (m : ℤ) :
    ∑ i : I, F (t⁻¹ * (φ ^ m * i) * t) = ∑ i : I, F (φ ^ m * i) := by sorry
