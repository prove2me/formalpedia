-- Prove2me | Theorems.Thm_JardenShami_Kappa_mk_eq
-- name    : JardenShami.Kappa.mk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:50.770729+00:00
-- url     : https://prove2.me/theorems/316747ef-6da1-4df0-8e42-ea910bb95adf
-- title:
--   Kappa: mk eq
-- statement:
--   AUX: not in paper. `#κ = κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L63-L64
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L63-L64

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.Kappa.mk_eq (κ : Cardinal.{w}) : #(Kappa κ) = κ := by sorry
