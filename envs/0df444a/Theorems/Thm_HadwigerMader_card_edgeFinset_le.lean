-- Prove2me | Theorems.Thm_HadwigerMader_card_edgeFinset_le
-- name    : HadwigerMader.card_edgeFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:27.546495+00:00
-- url     : https://prove2.me/theorems/df087de1-5b4e-54b1-bf28-88425a10e543
-- title:
--   Hadwiger Mader: card edge Finset le
-- statement:
--   A finite graph on `n ≥ 2` vertices without a `K₄` minor has at most `2n - 3` edges.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L67-L70
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L67-L70

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_CliqueMinors_card_edgeFinset_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.card_edgeFinset_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V := by sorry
