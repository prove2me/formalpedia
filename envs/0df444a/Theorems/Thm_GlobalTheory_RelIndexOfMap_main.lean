-- Prove2me | Theorems.Thm_GlobalTheory_RelIndexOfMap_main
-- name    : GlobalTheory.RelIndexOfMap.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:15.535222+00:00
-- url     : https://prove2.me/theorems/01d661c1-2edb-416c-986b-ad2ebe63f642
-- title:
--   Rel Index Of Map: main
-- statement:
--   The Rel Index Of Map construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexEqOfMap.lean#L65-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexEqOfMap.lean#L65-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexEqOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelIndexOfMap

theorem GlobalTheory.RelIndexOfMap.main : (let d1 : {G : Type} → [inst : Group G] → (M N : Subgroup G) → Subgroup G → G → Subgroup ↥(Subgroup.subgroupOf N M) := @(fun {G : Type} [Group G] (M N K : Subgroup G) (x : G) ↦ Subgroup.comap (MonoidHom.comp (Subgroup.subtype M) (Subgroup.subtype (Subgroup.subgroupOf N M))) (Subgroup.comap (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) x⁻¹)) K)); ∀ {G : Type} [inst : Group G] {M N K : Subgroup G} {ι : Type} [inst_1 : Fintype ι] {H : ι → Type} [inst_2 : (i : ι) → Group (H i)] (S : Subgroup G) [Subgroup.Normal S] (L : (i : ι) → G →* H i) (J Nn : (i : ι) → Subgroup (H i)), (∀ k ∈ K, ∀ (i : ι), (L i : G → H i) k ∈ J i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ J i) → y ∈ K) → S ≤ M → (∀ n ∈ N, ∀ (i : ι), (L i : G → H i) n ∈ Nn i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ Nn i) → y ∈ N) → (∀ (u : (i : ι) → H i), ∃ y ∈ S, ∀ (i : ι), (L i : G → H i) y = u i) → ∀ {δ r : G}, r ∈ S → ∀ (c h : (i : ι) → H i), (∀ (i : ι), (L i : G → H i) r = c i * h i) → (∀ (i : ι), c i ∈ J i) → (∀ (i : ι) (x : H i), ((L i : G → H i) δ * c i)⁻¹ * x * ((L i : G → H i) δ * c i) ∈ Nn i ↔ x ∈ Nn i) → Subgroup.relIndex (d1 M N K (δ * r)) (d1 M N K δ) = ∏ i : ι, Subgroup.relIndex (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i)) (Nn i ⊓ J i) ∧ Subgroup.relIndex (d1 M N K δ) (d1 M N K (δ * r)) = ∏ i : ι, Subgroup.relIndex (J i) (Nn i ⊓ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i))) := by sorry
