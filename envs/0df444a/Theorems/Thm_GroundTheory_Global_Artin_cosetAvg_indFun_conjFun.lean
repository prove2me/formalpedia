-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_cosetAvg_indFun_conjFun
-- name    : GroundTheory.Global.Artin.cosetAvg_indFun_conjFun
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:00.947452+00:00
-- url     : https://prove2.me/theorems/40860560-dec1-4374-87eb-d8e8d0bf4ceb
-- title:
--   Artin: coset Avg ind Fun conj Fun
-- statement:
--   The Artin construction uses the coset Avg ind Fun conj Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L222-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L222-L319

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
variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}
open Classical

theorem GroundTheory.Global.Artin.cosetAvg_indFun_conjFun [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) (f : H → ℂ) (x : G)
    (φx : H) (hφx : ∃ i ∈ (MulAut.conj x • I : Subgroup G),
      (φx : G) = x * φ ^ (frobIndex H D I x : ℤ) * x⁻¹ * i) (m : ℤ) :
    (Nat.card I : ℂ)⁻¹ * ∑ i : I,
        indFun ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D x f)
          ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩ =
      if (frobIndex H D I x : ℤ) ∣ m then
        (frobIndex H D I x : ℂ) *
          cosetAvg ((MulAut.conj x • I : Subgroup G).subgroupOf H) φx f (m / frobIndex H D I x)
      else 0 := by sorry
