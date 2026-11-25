-- Prove2me | Theorems.Thm_HadwigerMader_isMinor_K5_of_card_edgeFinset
-- name    : HadwigerMader.isMinor_K5_of_card_edgeFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:56:15.547588+00:00
-- url     : https://prove2.me/theorems/bf6fa71e-95ee-4b95-8a6e-b112ec0c1afa
-- title:
--   Hadwiger Mader: is Minor K5 of card edge Finset
-- statement:
--   **Mader (1968).** A finite graph on `n ≥ 3` vertices with at least `3n - 5` edges has a `K₅`
--   minor.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L74-L82
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L74-L82

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_CliqueMinors_isMinor_K5_of_card_edgeFinset

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.isMinor_K5_of_card_edgeFinset [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) :
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by sorry
