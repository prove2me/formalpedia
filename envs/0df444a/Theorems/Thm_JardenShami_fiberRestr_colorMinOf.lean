-- Prove2me | Theorems.Thm_JardenShami_fiberRestr_colorMinOf
-- name    : JardenShami.fiberRestr_colorMinOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:42.961548+00:00
-- url     : https://prove2.me/theorems/28b0bac3-2ac6-4bdf-9715-fe237090ac8a
-- title:
--   Jarden Shami: fiber Restr color Min Of
-- statement:
--   AUX: not in paper. `T(C_f)` for `C_f(α,β) = f(α)`: the graphs of `f ↾ β`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L661-L665
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L661-L665

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

theorem JardenShami.fiberRestr_colorMinOf (f : Kappa κ → Fin 2) (δ β : Kappa κ) (hβ : β ≤ δ) :
    fiberRestr (colorMinOf f) δ β hβ = {p | p.1 < β ∧ p.2 = f p.1} := by sorry
