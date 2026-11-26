-- Prove2me | Theorems.Thm_GRH_centered_prefix_character_unit_rows
-- name    : GRH.centered_prefix_character_unit_rows
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T17:44:06.742834+00:00
-- url     : https://prove2.me/theorems/1c579487-2549-4d89-a182-db858187538b
-- title:
--   Exact unit rows for the centered prefixes of a nonprincipal Dirichlet character
-- statement:
--   The sum on a complete period of unit residues is zero. At a positive residue the prefix minus one equals the character evaluated on the unit residues from two through that residue. At residue zero the centered value is minus one.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_CharacterMoment

open GRH.CharacterMoment

theorem GRH.centered_prefix_character_unit_rows (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (∑ a ∈ units q, χ (a:ZMod q))=0 ∧ ∀ n : ℕ,
      (∑ k ∈ Finset.range n,χ ((k+1:ℕ):ZMod q))-1 =
        if n%q=0 then -1 else ∑ a ∈ units q,(entry (n%q) a:ℂ)*χ (a:ZMod q) := by sorry
