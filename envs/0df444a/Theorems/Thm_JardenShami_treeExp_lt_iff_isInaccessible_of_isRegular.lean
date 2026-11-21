-- Prove2me | Theorems.Thm_JardenShami_treeExp_lt_iff_isInaccessible_of_isRegular
-- name    : JardenShami.treeExp_lt_iff_isInaccessible_of_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:25.519965+00:00
-- url     : https://prove2.me/theorems/dc275451-6a1f-42a0-99b8-d744e0becfdc
-- title:
--   Jarden Shami: tree Exp lt iff is Inaccessible of is Regular
-- statement:
--   AUX: not in paper. A strengthening of Theorem 6.4: for every uncountable regular cardinal `κ`,
--   `λ^{μ,tr} < κ` for each `λ, μ < κ` (infinite `μ ≤ λ`, as in Theorem 6.4) iff `κ` is strongly
--   inaccessible.
--   Neither the tree property, which is assumed in Theorem 6.4 of the paper, nor Fact 6.3, which the
--   paper's proof uses, is needed; hence this statement is stronger than Theorem 6.4 of the paper.
--   `treeExp_lt_iff_isInaccessible` (Theorem 6.4) is a thin wrapper around it.
--   Proof: (⇒) by induction on cardinals `ν < κ`, `2^ν < κ`, applying the hypothesis to the full
--   binary tree `2^{<ν}` (`two_power_lt_of_treeExp_lt`); Fact 6.3 is not used. (⇐) from Remark 6.2
--   and `λ^μ < κ` for strongly inaccessible `κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L371-L381
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L371-L381

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.treeExp_lt_iff_isInaccessible_of_isRegular (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := by sorry
