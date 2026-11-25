-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_cosetAvg_indFun
-- name    : GroundTheory.Global.Artin.cosetAvg_indFun
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:11.703806+00:00
-- url     : https://prove2.me/theorems/43bef036-7741-56f0-b0a9-12b143e38592
-- title:
--   Artin: coset Avg ind Fun
-- statement:
--   The Artin construction uses the coset Avg ind Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L329-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean#L329-L355

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

theorem GroundTheory.Global.Artin.cosetAvg_indFun [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) (φx : DoubleCoset.Quotient (H : Set G) D → H)
    (hφx : ∀ q, ∃ i ∈ (MulAut.conj (x q) • I : Subgroup G),
      (φx q : G) = x q * φ ^ (frobIndex H D I (x q) : ℤ) * (x q)⁻¹ * i) (m : ℤ) :
    cosetAvg I φ (indFun H.subtype f) m =
      ∑ q, if (frobIndex H D I (x q) : ℤ) ∣ m then
        (frobIndex H D I (x q) : ℂ) *
          cosetAvg ((MulAut.conj (x q) • I : Subgroup G).subgroupOf H) (φx q) f
            (m / frobIndex H D I (x q))
      else 0 := by sorry
