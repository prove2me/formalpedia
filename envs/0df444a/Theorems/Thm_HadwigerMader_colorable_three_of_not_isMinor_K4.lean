-- Prove2me | Theorems.Thm_HadwigerMader_colorable_three_of_not_isMinor_K4
-- name    : HadwigerMader.colorable_three_of_not_isMinor_K4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:36.721749+00:00
-- url     : https://prove2.me/theorems/9d2e135d-4917-5de7-8905-f6bc11331ef2
-- title:
--   Hadwiger Mader: colorable three of not is Minor K4
-- statement:
--   **Hadwiger's conjecture for `t = 4` (Hadwiger 1943, Dirac 1952).** A finite graph without a
--   `K₄` minor is 3-colourable.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L99-L102
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L99-L102

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_CliqueMinors_colorable_three_of_not_isMinor_K4

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.colorable_three_of_not_isMinor_K4 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : G.Colorable 3 := by sorry
