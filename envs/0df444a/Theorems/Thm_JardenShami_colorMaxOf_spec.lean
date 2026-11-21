-- Prove2me | Theorems.Thm_JardenShami_colorMaxOf_spec
-- name    : JardenShami.colorMaxOf_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:58.974443+00:00
-- url     : https://prove2.me/theorems/f67620b7-9cd0-4c09-9a2b-fb638a989430
-- title:
--   Jarden Shami: color Max Of spec
-- statement:
--   **Remark 4.8** (Section 4). If `f : κ → 2` is not eventually constant, then `C_f`
--   (`C_f(α,β) = f(β)`) is locally additive and *-locally additive, and
--   `T(C_f) = ^{<κ}{0} ∪ ^{<κ}{1}` (the constant functions with domain some `β < κ`).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L710-L737
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L710-L737

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

theorem JardenShami.colorMaxOf_spec (f : Kappa κ → Fin 2)
    (hf : ¬ ∃ (α₀ : Kappa κ) (i : Fin 2), ∀ β, α₀ ≤ β → f β = i) :
    IsLocallyAdditive (colorMaxOf f) ∧ IsStarLocallyAdditive (colorMaxOf f) ∧
      treeOfColoring (colorMaxOf f) =
        {g | ∃ (β : Kappa κ) (i : Fin 2), g = {p | p.1 < β ∧ p.2 = i}} := by sorry
