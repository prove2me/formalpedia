-- Prove2me | Theorems.Thm_JardenShami_mk_binTree_le
-- name    : JardenShami.mk_binTree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:21.452114+00:00
-- url     : https://prove2.me/theorems/c56382c8-ddcd-427d-919f-1dab8a9daaef
-- title:
--   Jarden Shami: mk bin Tree le
-- statement:
--   AUX: not in paper. `|2^{<ν}| ≤ Σ_{β<ν} 2^{|β|}`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L257-L282
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L257-L282

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {ν : Cardinal.{w}}

theorem JardenShami.mk_binTree_le :
    #(binTree ν) ≤ Cardinal.sum fun β : Kappa ν => (2 : Cardinal.{w}) ^ #(Set.Iio β) := by sorry
