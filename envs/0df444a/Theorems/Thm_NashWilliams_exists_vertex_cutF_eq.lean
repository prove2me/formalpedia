-- Prove2me | Theorems.Thm_NashWilliams_exists_vertex_cutF_eq
-- name    : NashWilliams.exists_vertex_cutF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T17:59:51.149921+00:00
-- url     : https://prove2.me/theorems/b34d200c-3754-4b4b-b4ba-017fc89713b7
-- title:
--   Nash Williams: exists vertex cut F eq
-- statement:
--   **Mader-type lemma.** If `Req K T` holds (with `K ≥ 1` and `|T| ≥ 2`) but fails after deleting
--   any active edge, then some vertex of `T` has degree exactly `K`.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Mader.lean#L92-L158
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Mader.lean#L92-L158

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Mader
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem NashWilliams.exists_vertex_cutF_eq {K : ℕ} (hK : 1 ≤ K) {T : Finset V} (hT : 1 < T.card)
    {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F) (hreq : Req K T ends F)
    (hmin : ∀ i ∈ F, ¬ Req K T ends (F.erase i)) : ∃ s ∈ T, cutF ends F {s} = K := by sorry
