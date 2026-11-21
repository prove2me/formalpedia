-- Prove2me | Theorems.Thm_JardenShami_treeColoring_eq_iff_mem_histFun
-- name    : JardenShami.treeColoring_eq_iff_mem_histFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:51.36856+00:00
-- url     : https://prove2.me/theorems/00dcd53f-786d-41af-a013-c963841aee17
-- title:
--   Jarden Shami: tree Coloring eq iff mem hist Fun
-- statement:
--   **Claim 4.16** (Section 4, inside the proof of Theorem 4.15,
--   `\label{claim for theorem 4.21}`). For `α < β ≤ δ < κ` and `i < μ_α`:
--   `(C(·,δ) ↾ β)(α) = i` iff `f_{t_β^{C(β,δ)}}(α) = t^i_α`.
--   CHANGED w.r.t. the paper: the paper's display reads "`(C(·,δ)↾β)(α)` if and only if ..." with
--   the right-hand side `= i` missing; the intended `= i` (as in clause (1) of its proof) is used.
--   Since `α < β`, `(C(·,δ)↾β)(α) = C(α,δ)`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1029-L1046
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1029-L1046

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

theorem JardenShami.treeColoring_eq_iff_mem_histFun (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {α β δ : Kappa κ} (hαβ : α < β) (hβδ : β ≤ δ) {i : Ordinal.{w}}
    (hi : i < (#(Lev T (α : Ordinal.{w}))).ord) :
    ((C.color α δ (hαβ.trans_le hβδ) : Ordinal.{w}) = i) ↔
      ((α : Ordinal.{w}), e.t α i) ∈ histFun (e.node C β δ hβδ) := by sorry
