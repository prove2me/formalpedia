-- Prove2me | Theorems.Thm_JardenShami_treeExp_lt_iff_isInaccessible
-- name    : JardenShami.treeExp_lt_iff_isInaccessible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:25.510204+00:00
-- url     : https://prove2.me/theorems/104c4880-fcc4-4e6e-926f-51fc0871ffbe
-- title:
--   Jarden Shami: tree Exp lt iff is Inaccessible
-- statement:
--   **Theorem 6.4** (Section 6, `\label{theorem 5.4}`). Let `κ` be an uncountable regular cardinal.
--   The following are equivalent: (1) `λ^{μ,tr} < κ` for each `λ, μ < κ`; (2) `κ` is strongly
--   inaccessible.
--   In (1), `λ^{μ,tr}` is taken only where Definition 6.1 defines it: infinite `μ ≤ λ`.
--   The paper also assumes that `κ` satisfies the tree property, and its proof of (1) ⇒ (2) uses
--   Fact 6.3. Neither is needed, so this statement is stronger than Theorem 6.4 of the paper.
--   It is a thin wrapper around the AUX statement `treeExp_lt_iff_isInaccessible_of_isRegular`; the
--   proof does not follow the paper's proof.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L391-L395
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L391-L395

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.treeExp_lt_iff_isInaccessible (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := by sorry
