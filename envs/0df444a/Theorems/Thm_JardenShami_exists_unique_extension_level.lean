-- Prove2me | Theorems.Thm_JardenShami_exists_unique_extension_level
-- name    : JardenShami.exists_unique_extension_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:48.097087+00:00
-- url     : https://prove2.me/theorems/922dd10f-0d2d-4b91-b7ab-cda8c024b818
-- title:
--   Jarden Shami: exists unique extension level
-- statement:
--   **Claim 7.9** (Section 7, `\label{argue}`, inside Case A of the proof of Claim 7.8). Let
--   `λ` be regular and `T` a well-pruned `κ`-tree whose levels have size `< λ`.
--   For every ordinal `α < κ` with `cf(α) = λ` there is an ordinal `q(α) < α` such that for every
--   ordinal `β` with `q(α) < β < α` and any `a ∈ Lev_{q(α)}(T)` there are no two distinct
--   `b, c ∈ Lev_β(T)` with `a < b` and `a < c`. (In the paper `κ` is regular and `λ < κ`; these
--   hypotheses are not needed and are not assumed here.)
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L616-L639
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L616-L639

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.exists_unique_extension_level (κ lam : Cardinal.{w})
    (hlamreg : lam.IsRegular) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hwp : WellPruned T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∀ α : Ordinal.{w}, α < κ.ord → α.cof = lam →
      ∃ q < α, ∀ β : Ordinal.{w}, q < β → β < α →
        ∀ a ∈ Lev T q, ∀ b ∈ Lev T β, ∀ c ∈ Lev T β, a < b → a < c → b = c := by sorry
