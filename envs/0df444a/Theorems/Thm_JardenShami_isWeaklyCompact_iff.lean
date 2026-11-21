-- Prove2me | Theorems.Thm_JardenShami_isWeaklyCompact_iff
-- name    : JardenShami.isWeaklyCompact_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:36.899386+00:00
-- url     : https://prove2.me/theorems/19615a11-8115-4724-829b-22e5597af33b
-- title:
--   Jarden Shami: is Weakly Compact iff
-- statement:
--   **Corollary 6.5** (Section 6). Let `κ` be an uncountable cardinal. Then `κ` is weakly compact
--   if and only if (1) `κ` is regular, (2) `κ` satisfies the tree property and (3) `λ^{μ,tr} < κ` for
--   each `λ, μ < κ` (as in Theorem 6.4: infinite `μ ≤ λ`).
--   In the paper this goes through Theorem 6.4, whose proof uses Fact 6.3. Fact 6.3 is not needed
--   (see `treeExp_lt_iff_isInaccessible`), so this statement, which has no Fact 6.3 hypothesis, is
--   stronger than Corollary 6.5 of the paper.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L403-L412
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L403-L412

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.isWeaklyCompact_iff (κ : Cardinal.{w}) (hunc : ℵ₀ < κ) :
    IsWeaklyCompact κ ↔
      κ.IsRegular ∧ NoAronszajn κ ∧
        ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ := by sorry
