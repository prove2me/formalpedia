-- Prove2me | Theorems.Thm_JardenShami_Pairs_mk_inj
-- name    : JardenShami.Pairs.mk_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:14.698181+00:00
-- url     : https://prove2.me/theorems/78403943-33bc-40b6-a089-b562c275498e
-- title:
--   Pairs: mk inj
-- statement:
--   AUX: not in paper. `{a, b} = {c, d}` with `a < b` and `c < d` forces `a = c` and `b = d`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L36-L42
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L36-L42

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami

theorem JardenShami.Pairs.mk_inj {A : Type*} [LinearOrder A] {a b c d : A} (hab : a < b) (hcd : c < d)
    (h : Pairs.mk a b hab.ne = Pairs.mk c d hcd.ne) : a = c ∧ b = d := by sorry
