-- Prove2me | Theorems.Thm_JardenShami_fiberRestr_eq_iff_histFun_eq
-- name    : JardenShami.fiberRestr_eq_iff_histFun_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:54.659994+00:00
-- url     : https://prove2.me/theorems/4274b945-9e17-4750-82ef-a559204dc630
-- title:
--   Jarden Shami: fiber Restr eq iff hist Fun eq
-- statement:
--   **Claim 4.17** (Section 4, inside the proof of Theorem 4.15,
--   `\label{claim result of claim for theorem 4.21}`). For `β₁ ≤ δ₁` and `β₂ ≤ δ₂`:
--   `C(·,δ₁) ↾ β₁ = C(·,δ₂) ↾ β₂` iff `f_{t_{β₁}^{C(β₁,δ₁)}} = f_{t_{β₂}^{C(β₂,δ₂)}}`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1088-L1094
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1088-L1094

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

theorem JardenShami.fiberRestr_eq_iff_histFun_eq (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) = histFun (e.node C β₂ δ₂ h₂) := by sorry
