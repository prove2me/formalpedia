-- Prove2me | Theorems.Thm_JardenShami_Kappa_mk_Iic_lt
-- name    : JardenShami.Kappa.mk_Iic_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:02.56056+00:00
-- url     : https://prove2.me/theorems/7bf3e048-aea9-43fa-9e3f-5cc58cd90cfd
-- title:
--   Kappa: mk Iic lt
-- statement:
--   AUX: not in paper. For infinite `κ`, every initial segment `{y : y ≤ x}` of `κ` has size
--   `< κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L70-L76
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L70-L76

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}

theorem JardenShami.Kappa.mk_Iic_lt (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : #(Set.Iic x) < κ := by sorry
