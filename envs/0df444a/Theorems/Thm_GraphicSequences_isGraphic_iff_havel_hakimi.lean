-- Prove2me | Theorems.Thm_GraphicSequences_isGraphic_iff_havel_hakimi
-- name    : GraphicSequences.isGraphic_iff_havel_hakimi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:16:31.925033+00:00
-- url     : https://prove2.me/theorems/b95f2e36-74f6-4486-be09-451f63d46691
-- title:
--   Graphic Sequences: is Graphic iff havel hakimi
-- statement:
--   **Havel–Hakimi theorem (Havel 1955, Hakimi 1962).** A non-increasing sequence `d₀, …, d_m` is
--   graphic if and only if `d₀ ≤ m`, the terms `d₁, …, d_{d₀}` are positive, and its Havel–Hakimi
--   reduction is graphic.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/Solution.lean#L46-L49
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/Solution.lean#L46-L49

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Definitions.Def_DegreeSequences_Solution
public import Theorems.Thm_DegreeSequences_isGraphic_iff_havel_hakimi

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open GraphicSequences

theorem GraphicSequences.isGraphic_iff_havel_hakimi {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧
      IsGraphic (havelHakimi d) := by sorry
