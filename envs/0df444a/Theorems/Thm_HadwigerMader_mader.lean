-- Prove2me | Theorems.Thm_HadwigerMader_mader
-- name    : HadwigerMader.mader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:39.963771+00:00
-- url     : https://prove2.me/theorems/70025959-4acd-43c0-a35c-bfabcf89bda6
-- title:
--   Hadwiger Mader: mader
-- statement:
--   **Mader's theorem (1967).** A nonempty finite graph whose average degree is at least
--   `2 ^ (r - 2)`, i.e. `2 ^ r · |V| ≤ 8 · |E|`, has the complete graph `K_r` as a minor.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L55-L58
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L55-L58

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_CliqueMinors_mader

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.mader [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : 2 ^ r * Fintype.card V ≤ 8 * G.edgeFinset.card) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by sorry
