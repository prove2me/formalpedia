-- Prove2me | Theorems.Thm_GlobalTheory_relIndex_inf_conj_eq_finprod_of_restricted_product
-- name    : GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:27.093877+00:00
-- url     : https://prove2.me/theorems/d53aa3a9-6689-443a-8d8d-915a093225b8
-- title:
--   Global Theory: rel Index inf conj eq finprod of restricted product
-- statement:
--   The Global Theory construction uses the rel Index inf conj eq finprod of restricted product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexInfConjEqFinprodRestrictedProduct.lean#L7-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexInfConjEqFinprodRestrictedProduct.lean#L7-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexInfConjEqFinprodRestrictedProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory

theorem GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product
    (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G)
    (hglue : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (hC : ∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i)
    (hCT : ∀ i, CH i ≤ TH i)
    (_hloc : ∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧
      (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0)
    (hCK : ∀ᶠ i in cofinite, CH i ≤ KH i) :
    (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C =
      ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by sorry
