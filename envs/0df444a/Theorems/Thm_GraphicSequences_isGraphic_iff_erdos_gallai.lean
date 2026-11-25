-- Prove2me | Theorems.Thm_GraphicSequences_isGraphic_iff_erdos_gallai
-- name    : GraphicSequences.isGraphic_iff_erdos_gallai
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:37.383851+00:00
-- url     : https://prove2.me/theorems/4f2ac403-4dd0-46de-970f-0847f0389dbd
-- title:
--   Graphic Sequences: is Graphic iff erdos gallai
-- statement:
--   **Erdős–Gallai theorem (1960).** A non-increasing sequence of natural numbers is the degree
--   sequence of a simple graph if and only if its sum is even and every initial segment satisfies the
--   Erdős–Gallai inequality.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/Solution.lean#L38-L41
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/Solution.lean#L38-L41

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Definitions.Def_DegreeSequences_Solution
public import Theorems.Thm_DegreeSequences_isGraphic_iff_erdos_gallai

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open GraphicSequences

theorem GraphicSequences.isGraphic_iff_erdos_gallai {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ Even (∑ i, d i) ∧
      ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by sorry
