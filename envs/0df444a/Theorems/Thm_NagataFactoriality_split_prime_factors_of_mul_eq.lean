-- Prove2me | Theorems.Thm_NagataFactoriality_split_prime_factors_of_mul_eq
-- name    : NagataFactoriality.split_prime_factors_of_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:50.147811+00:00
-- url     : https://prove2.me/theorems/533c807a-122e-4b74-b9f0-810a0014b002
-- title:
--   Nagata Factoriality: split prime factors of mul eq
-- statement:
--   The Nagata Factoriality construction uses the split prime factors of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L190-L258
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L190-L258

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.split_prime_factors_of_mul_eq {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a b : α} (_hp : Irreducible p)
    (hEq : p * f.prod = a * b) :
    ∃ f₁ f₂ : Multiset α, ∃ a' b' : α,
      f₁ + f₂ = f ∧
      a = f₁.prod * a' ∧
      b = f₂.prod * b' ∧
      p = a' * b' := by sorry
