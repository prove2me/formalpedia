-- Prove2me | Theorems.Thm_JardenShami_Enumeration_node_spec
-- name    : JardenShami.Enumeration.node_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:38.651997+00:00
-- url     : https://prove2.me/theorems/3261d3d7-2eee-4d46-b262-30ee82cd3327
-- title:
--   Enumeration: node spec
-- statement:
--   AUX: not in paper. `t_β^{C(β,δ)} ∈ Lev_β(T)` and `t_β^{C(β,δ)} ≤ t^0_δ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1012-L1021
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1012-L1021

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

theorem JardenShami.Enumeration.node_spec (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β δ : Kappa κ} (h : β ≤ δ) :
    ht (e.node C β δ h) = β ∧ e.node C β δ h ≤ e.t δ 0 := by sorry
