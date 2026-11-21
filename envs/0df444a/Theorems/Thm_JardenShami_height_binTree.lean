-- Prove2me | Theorems.Thm_JardenShami_height_binTree
-- name    : JardenShami.height_binTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:04.966024+00:00
-- url     : https://prove2.me/theorems/2ec8fce2-d6a9-4d9d-9357-77679ee0847b
-- title:
--   Jarden Shami: height bin Tree
-- statement:
--   AUX: not in paper. The height of `2^{<ν}` is `ν`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L239-L254
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L239-L254

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {ν : Cardinal.{w}}

theorem JardenShami.height_binTree : height (binTree ν) = ν.ord := by sorry
