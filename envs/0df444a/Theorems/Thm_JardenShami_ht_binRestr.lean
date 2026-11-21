-- Prove2me | Theorems.Thm_JardenShami_ht_binRestr
-- name    : JardenShami.ht_binRestr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:24.319757+00:00
-- url     : https://prove2.me/theorems/35f7beff-5244-488e-b247-0de19457291d
-- title:
--   Jarden Shami: ht bin Restr
-- statement:
--   AUX: not in paper. The height of `f ↾ β` in `2^{<ν}` is `β`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L207-L236
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L207-L236

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {ν : Cardinal.{w}}

theorem JardenShami.ht_binRestr (f : Kappa ν → Fin 2) (β : Kappa ν) :
    ht (⟨binRestr f β, f, β, rfl⟩ : binTree ν) = (β : Ordinal.{w}) := by sorry
