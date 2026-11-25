-- Prove2me | Theorems.Thm_NashWilliams_split_all
-- name    : NashWilliams.split_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:11:57.988198+00:00
-- url     : https://prove2.me/theorems/c6b1855c-8114-598e-9ae6-4f1f3894e1d1
-- title:
--   Nash Williams: split all
-- statement:
--   **Complete splitting at `s`.**
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L101-L162
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L101-L162

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]

theorem NashWilliams.split_all {K : ℕ} (hK : 2 ≤ K) {T : Finset V} {s : V} :
    ∀ (m : ℕ) (ends : ι → V × V) (F : Finset ι), Inside T ends F → Req K (T.erase s) ends F →
      cutF ends F {s} = 2 * m →
      ∃ (ends' : ι → V × V) (F' : Finset ι), F'.card + m = F.card ∧ Inside T ends' F' ∧
        Req K (T.erase s) ends' F' ∧ cutF ends' F' {s} = 0 ∧
        ∀ o' : ι → Bool, ∃ o : ι → Bool, (∀ S, outCutF ends' o' F' S ≤ outCutF ends o F S) ∧
          m ≤ outCutF ends o F {s} ∧ m ≤ outCutF ends o F (T.erase s) := by sorry
