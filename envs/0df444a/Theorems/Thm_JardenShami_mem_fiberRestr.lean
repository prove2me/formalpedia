-- Prove2me | Theorems.Thm_JardenShami_mem_fiberRestr
-- name    : JardenShami.mem_fiberRestr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:36.099178+00:00
-- url     : https://prove2.me/theorems/daca6404-bf94-4b31-a2e7-dbbad17b1ecd
-- title:
--   Jarden Shami: mem fiber Restr
-- statement:
--   AUX: not in paper. Membership in the graph of `C(·,δ) ↾ β`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L555-L558
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L555-L558

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

theorem JardenShami.mem_fiberRestr {C : Coloring (Kappa κ) D} {δ β : Kappa κ} {hβ : β ≤ δ}
    {α : Kappa κ} {d : D} :
    (α, d) ∈ fiberRestr C δ β hβ ↔ ∃ h : α < β, d = C.color α δ (h.trans_le hβ) := by sorry
