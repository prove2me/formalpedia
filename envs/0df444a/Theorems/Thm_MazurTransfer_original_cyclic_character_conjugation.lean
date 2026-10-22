-- Prove2me | Theorems.Thm_MazurTransfer_original_cyclic_character_conjugation
-- name    : MazurTransfer.original_cyclic_character_conjugation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T22:10:25.775471+00:00
-- url     : https://prove2.me/theorems/c655c27e-9e41-4e68-ad75-18091a11b66c
-- statement:
--   Conjugating the original cyclic group automorphism through its given fixed group isomorphism commutes with every original character into that same cyclic group. The complete original proposition and helper type and the original conjugation constructor type and whole value are independently checked. All original group, cyclicity, fixed isomorphism, automorphism, character and element hypotheses are retained. Named downstream consumer: normalization of the same selected integral mu19 quotient arithmetic point label by its original bialgebra automorphism.

import Definitions.Def_MazurTransfer_OriginalCyclicCharacterConjugationData20261020
open MazurTransfer.CyclicCharacterConjugation

theorem MazurTransfer.original_cyclic_character_conjugation : ∀ {C P : Type} [Group C] [Group P] [IsCyclic P], ∀ (r : C ≃* P) (α : P ≃* P) (χ : C →* P) (c : C),
χ (conjugate r α c) = α (χ c) := by sorry
