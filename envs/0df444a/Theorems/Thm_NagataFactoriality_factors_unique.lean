-- Prove2me | Theorems.Thm_NagataFactoriality_factors_unique
-- name    : NagataFactoriality.factors_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:31.62834+00:00
-- url     : https://prove2.me/theorems/17a2b039-5b18-4d8e-ac80-67c8d980c340
-- title:
--   Nagata Factoriality: factors unique
-- statement:
--   The Nagata Factoriality construction uses the factors unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/UFD.lean#L52-L62
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/UFD.lean#L52-L62

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Definitions.Def_NagataFactoriality_Basic_UFD
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.factors_unique {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p)
    {a : α} (ha : a ≠ 0) {f : Multiset α}
    (hf : ∀ x ∈ f, Irreducible x)
    (hfa : Associated f.prod a) :
    letI : UniqueFactorizationMonoid α := ufd_of_factorization_and_primes hfac hprime
    FactorizationEquivalent f (UniqueFactorizationMonoid.factors a) := by sorry
