-- Prove2me | Theorems.Thm_HadwigerMader_colorable_two_of_not_isMinor_K3
-- name    : HadwigerMader.colorable_two_of_not_isMinor_K3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:54.933668+00:00
-- url     : https://prove2.me/theorems/e895ae07-759d-47b8-b3ec-834029968446
-- title:
--   Hadwiger Mader: colorable two of not is Minor K3
-- statement:
--   **Hadwiger's conjecture for `t = 3`.** A finite graph without a `K₃` minor (a forest) is
--   2-colourable.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L93-L95
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L93-L95

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_CliqueMinors_colorable_two_of_not_isMinor_K3

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.colorable_two_of_not_isMinor_K3 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) : G.Colorable 2 := by sorry
