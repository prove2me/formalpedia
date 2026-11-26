-- Prove2me | Theorems.Thm_NagataFactoriality_dvd_of_mul_eq_prime_factors
-- name    : NagataFactoriality.dvd_of_mul_eq_prime_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:26.973556+00:00
-- url     : https://prove2.me/theorems/5d26df78-0428-58aa-b309-dc393b956e10
-- title:
--   Nagata Factoriality: dvd of mul eq prime factors
-- statement:
--   The Nagata Factoriality construction uses the dvd of mul eq prime factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L109-L146
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L109-L146

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.dvd_of_mul_eq_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a c : α} (hp : Irreducible p)
    (hnot : ∀ q ∈ f, ¬ p ∣ q) (hEq : f.prod * a = p * c) : p ∣ a := by sorry
