-- Prove2me | Theorems.Thm_JardenShami_IsTreeColoring_color_eq
-- name    : JardenShami.IsTreeColoring.color_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:44.364907+00:00
-- url     : https://prove2.me/theorems/902b56d0-59c9-4797-8cd5-cf22db2a3155
-- title:
--   Is Tree Coloring: color eq
-- statement:
--   AUX: not in paper. Uniqueness in Definition 4.11: if `i < μ_α` and `t^i_α ≤ t^0_δ` then
--   `C(T,e)(α,δ) = i`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L811-L818
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L811-L818

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.IsTreeColoring.color_eq {e : Enumeration κ T}
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) {α δ : Kappa κ}
    (h : α < δ) {i : Ordinal.{w}} (hi : i < (#(Lev T (α : Ordinal.{w}))).ord)
    (hle : e.t α i ≤ e.t δ 0) : (C.color α δ h : Ordinal.{w}) = i := by sorry
