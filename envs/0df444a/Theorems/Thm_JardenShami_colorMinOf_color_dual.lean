-- Prove2me | Theorems.Thm_JardenShami_colorMinOf_color_dual
-- name    : JardenShami.colorMinOf_color_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:44.293324+00:00
-- url     : https://prove2.me/theorems/3bb487ea-d03e-4f91-a9d9-08078ed6068e
-- title:
--   Jarden Shami: color Min Of color dual
-- statement:
--   AUX: not in paper. For the reverse order: `C_f(a,b) = f(b)` for `b < a`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L655-L658
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L655-L658

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}

theorem JardenShami.colorMinOf_color_dual (f : Kappa κ → Fin 2) (a b : (Kappa κ)ᵒᵈ) (h : a < b) :
    Coloring.color (A := (Kappa κ)ᵒᵈ) (colorMinOf f) a b h = f (OrderDual.ofDual b) := by sorry
