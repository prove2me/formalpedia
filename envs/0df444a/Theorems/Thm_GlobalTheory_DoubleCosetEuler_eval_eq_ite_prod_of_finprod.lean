-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetEuler_eval_eq_ite_prod_of_finprod
-- name    : GlobalTheory.DoubleCosetEuler.eval_eq_ite_prod_of_finprod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:58.59983+00:00
-- url     : https://prove2.me/theorems/ff39330b-1125-4505-abdb-dc68b39cd8f9
-- title:
--   Double Coset Euler: eval eq ite prod of finprod
-- statement:
--   The Double Coset Euler construction uses the eval eq ite prod of finprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetEqFinprodLocalSums.lean#L36-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetEqFinprodLocalSums.lean#L36-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums
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
open GlobalTheory GlobalTheory.DoubleCosetEuler

theorem GlobalTheory.DoubleCosetEuler.eval_eq_ite_prod_of_finprod (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ) (S0 : Finset ι)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0)
    (hprod : ∀ g, s g = ∏ᶠ i, s' i (p i g)) (g : G) :
    s g = if ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k then ∏ i ∈ S0, s' i (p i g) else 0 := by sorry
