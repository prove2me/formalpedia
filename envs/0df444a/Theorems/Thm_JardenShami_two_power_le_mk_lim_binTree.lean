-- Prove2me | Theorems.Thm_JardenShami_two_power_le_mk_lim_binTree
-- name    : JardenShami.two_power_le_mk_lim_binTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:19.325852+00:00
-- url     : https://prove2.me/theorems/e4ce3e9a-8589-4456-9d29-8e67d73cd6ce
-- title:
--   Jarden Shami: two power le mk lim bin Tree
-- statement:
--   AUX: not in paper. For infinite `ν`, `2^{<ν}` has at least `2^ν` cofinal branches.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L285-L334
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L285-L334

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {ν : Cardinal.{w}}

theorem JardenShami.two_power_le_mk_lim_binTree (hν : ℵ₀ ≤ ν) : 2 ^ ν ≤ #(Lim (binTree ν)) := by sorry
