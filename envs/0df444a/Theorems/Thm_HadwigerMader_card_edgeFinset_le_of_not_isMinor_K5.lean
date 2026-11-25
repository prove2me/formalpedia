-- Prove2me | Theorems.Thm_HadwigerMader_card_edgeFinset_le_of_not_isMinor_K5
-- name    : HadwigerMader.card_edgeFinset_le_of_not_isMinor_K5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:50.884893+00:00
-- url     : https://prove2.me/theorems/afce241a-0108-46fc-bebd-86a9e20564f9
-- title:
--   Hadwiger Mader: card edge Finset le of not is Minor K5
-- statement:
--   A finite graph on `n ≥ 3` vertices without a `K₅` minor has at most `3n - 6` edges.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L85-L89
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L85-L89

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.card_edgeFinset_le_of_not_isMinor_K5 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
