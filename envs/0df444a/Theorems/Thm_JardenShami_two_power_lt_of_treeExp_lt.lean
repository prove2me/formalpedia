-- Prove2me | Theorems.Thm_JardenShami_two_power_lt_of_treeExp_lt
-- name    : JardenShami.two_power_lt_of_treeExp_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:23.672179+00:00
-- url     : https://prove2.me/theorems/2b4863fd-ca8f-475e-b328-f12c8268aab6
-- title:
--   Jarden Shami: two power lt of tree Exp lt
-- statement:
--   AUX: not in paper. Direction (1) ⇒ (2) of Theorem 6.4 without Fact 6.3 and without the tree
--   property: if `κ` is regular and uncountable and `λ^{μ,tr} < κ` for all infinite `μ ≤ λ < κ`,
--   then `2^ν < κ` for all `ν < κ` (apply the hypothesis to the full binary tree `2^{<ν}`).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L341-L360
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L341-L360

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.two_power_lt_of_treeExp_lt {κ : Cardinal.{w}} (hreg : κ.IsRegular)
    (h : ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) :
    ∀ ν < κ, 2 ^ ν < κ := by sorry
