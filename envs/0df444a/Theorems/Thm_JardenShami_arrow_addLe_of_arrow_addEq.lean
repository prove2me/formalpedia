-- Prove2me | Theorems.Thm_JardenShami_arrow_addLe_of_arrow_addEq
-- name    : JardenShami.arrow_addLe_of_arrow_addEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:14.179919+00:00
-- url     : https://prove2.me/theorems/779ebb7e-581b-45d2-ac5c-c08edc357b03
-- title:
--   Jarden Shami: arrow add Le of arrow add Eq
-- statement:
--   AUX: not in paper. Enlarging the set of colors (the gap noted in row 3.1 of FIDELITY.md):
--   since Definition 2.1 counts the codomain, an additive coloring with at most `κ` colors is also an
--   additive coloring with exactly `κ` colors (compose with an injection `D ↪ D'`, `#D' = κ`), and it
--   has the same homogeneous sets. Hence `F₁ → (F₂)_{add_κ}` implies the same arrow for additive
--   colorings with `≤ κ` colors.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L183-L201
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L183-L201

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {X : Type w} [LinearOrder X]

theorem JardenShami.arrow_addLe_of_arrow_addEq (κ : Cardinal.{v}) (F₁ F₂ : Set (Set X))
    (h : Arrow F₁ F₂ (addEq κ)) : Arrow F₁ F₂ (fun _ D C => IsAdditive C ∧ #D ≤ κ) := by sorry
