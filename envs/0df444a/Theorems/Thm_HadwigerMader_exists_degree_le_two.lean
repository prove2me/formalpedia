-- Prove2me | Theorems.Thm_HadwigerMader_exists_degree_le_two
-- name    : HadwigerMader.exists_degree_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:09.798422+00:00
-- url     : https://prove2.me/theorems/8e98ed51-e8c0-5c7e-a3ac-0d111a3a6709
-- title:
--   Hadwiger Mader: exists degree le two
-- statement:
--   **Dirac (1952).** A nonempty finite graph without a `K₄` minor has a vertex of degree at most
--   two.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L62-L64
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L62-L64

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_CliqueMinors_exists_degree_le_two

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.exists_degree_le_two [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : ∃ v, G.degree v ≤ 2 := by sorry
