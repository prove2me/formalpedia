-- Prove2me | Theorems.Thm_JardenShami_Coloring_color_dual
-- name    : JardenShami.Coloring.color_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:30.925009+00:00
-- url     : https://prove2.me/theorems/b5838074-e4ed-487e-ab14-fe3f5309306f
-- title:
--   Coloring: color dual
-- statement:
--   AUX: not in paper. A pair read in the reverse order.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L54-L58
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L54-L58

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.Coloring.color_dual {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D)
    (a b : Aᵒᵈ) (h : a < b) :
    Coloring.color (A := Aᵒᵈ) C a b h =
      C.color (OrderDual.ofDual b) (OrderDual.ofDual a) h := by sorry
