-- Prove2me | Theorems.Thm_NagataFactoriality_palomar_nagata_factoriality
-- name    : NagataFactoriality.palomar_nagata_factoriality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:27.379841+00:00
-- url     : https://prove2.me/theorems/706e5931-647f-5543-b678-9c41752dda86
-- title:
--   Nagata Factoriality: palomar nagata factoriality
-- statement:
--   The Nagata Factoriality construction uses the palomar nagata factoriality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/Solution.lean#L14-L22
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/Solution.lean#L14-L22

import Definitions.Def_NagataFactoriality_Applications_Laurent
import Definitions.Def_NagataFactoriality_Solution
set_option autoImplicit false
open NagataFactoriality
open Polynomial

theorem NagataFactoriality.palomar_nagata_factoriality
    {R T : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization S T] [IsDomain T]
    (hS : ∀ s : R, s ∈ S →
      ∃ f : Multiset R, (∀ q ∈ f, q ∈ S ∧ Prime q) ∧ f.prod = s)
    (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by sorry
