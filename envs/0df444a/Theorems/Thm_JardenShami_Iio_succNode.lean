-- Prove2me | Theorems.Thm_JardenShami_Iio_succNode
-- name    : JardenShami.Iio_succNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:41.508179+00:00
-- url     : https://prove2.me/theorems/403a6eaa-d3b2-4340-816b-d2f0b21de624
-- title:
--   Jarden Shami: Iio succ Node
-- statement:
--   AUX: not in paper. The predecessors of `succNode t` are exactly the nodes `≤ t`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L381-L391
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L381-L391

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

theorem JardenShami.Iio_succNode {t : T} (ht' : ¬ IsLeaf t) : Set.Iio (succNode ht') = Set.Iic t := by sorry
