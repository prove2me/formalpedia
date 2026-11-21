-- Prove2me | Theorems.Thm_JardenShami_exists_big_above
-- name    : JardenShami.exists_big_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:33.079766+00:00
-- url     : https://prove2.me/theorems/eace27ca-44a8-4189-8cea-feed675c7d41
-- title:
--   Jarden Shami: exists big above
-- statement:
--   AUX: not in paper. In a `κ`-tree (`κ` regular): if `x` has `≥ κ` nodes above it and
--   `ht x < α < κ`, then some `y ∈ Lev_α(T)` with `x < y` has `≥ κ` nodes above it.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L384-L404
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L384-L404

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.exists_big_above {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T) {x : T}
    (hx : κ ≤ #(Set.Ici x)) {α : Ordinal.{w}} (hxα : ht x < α) (hα : α < κ.ord) :
    ∃ y ∈ Lev T α, x < y ∧ κ ≤ #(Set.Ici y) := by sorry
