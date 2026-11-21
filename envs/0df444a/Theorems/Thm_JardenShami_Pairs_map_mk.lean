-- Prove2me | Theorems.Thm_JardenShami_Pairs_map_mk
-- name    : JardenShami.Pairs.map_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:15.026355+00:00
-- url     : https://prove2.me/theorems/f13a2a57-bf13-4028-aaee-e2132430a10d
-- title:
--   Pairs: map mk
-- statement:
--   AUX: not in paper. `f {a, b} = {f a, f b}`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L67-L69
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L67-L69

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami

theorem JardenShami.Pairs.map_mk {A B : Type*} (f : A → B) (hf : Function.Injective f) (a b : A)
    (h : a ≠ b) : Pairs.map f hf (Pairs.mk a b h) = Pairs.mk (f a) (f b) (hf.ne h) := by sorry
