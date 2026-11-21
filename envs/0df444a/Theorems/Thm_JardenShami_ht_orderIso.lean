-- Prove2me | Theorems.Thm_JardenShami_ht_orderIso
-- name    : JardenShami.ht_orderIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:39.770183+00:00
-- url     : https://prove2.me/theorems/c9f6655a-aa39-4720-8666-4d1e22f533af
-- title:
--   Jarden Shami: ht order Iso
-- statement:
--   AUX: not in paper. Order isomorphisms of trees preserve heights.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L365-L374
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L365-L374

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.ht_orderIso {P Q : Type u} [PartialOrder P] [IsTree P] [PartialOrder Q] [IsTree Q]
    (e : P ≃o Q) (t : P) : ht (e t) = ht t := by sorry
