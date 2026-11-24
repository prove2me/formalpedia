-- Prove2me | Theorems.Thm_GlobalTheory_LocalGrouping_finprod_finsum_eq
-- name    : GlobalTheory.LocalGrouping.finprod_finsum_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:27.349257+00:00
-- url     : https://prove2.me/theorems/c718ff69-264f-4808-92ec-1dd81a227d32
-- title:
--   Local Grouping: finprod finsum eq
-- statement:
--   The Local Grouping construction uses the finprod finsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L19-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L19-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount
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
open GlobalTheory GlobalTheory.LocalGrouping
open Function

theorem GlobalTheory.LocalGrouping.finprod_finsum_eq (I : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0) :
    ∏ᶠ i ∈ S, ∑ᶠ d, B i d = ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by sorry
