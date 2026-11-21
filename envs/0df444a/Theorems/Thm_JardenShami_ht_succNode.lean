-- Prove2me | Theorems.Thm_JardenShami_ht_succNode
-- name    : JardenShami.ht_succNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:34.71799+00:00
-- url     : https://prove2.me/theorems/74773cc6-b2d8-4722-b4c8-b5c3a4e42a95
-- title:
--   Jarden Shami: ht succ Node
-- statement:
--   AUX: not in paper. `ht (succNode t) = ht t + 1`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L394-L403
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L394-L403

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

theorem JardenShami.ht_succNode {t : T} (ht' : ¬ IsLeaf t) : ht (succNode ht') = Order.succ (ht t) := by sorry
