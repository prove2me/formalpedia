-- Prove2me | Theorems.Thm_JardenShami_mk_lim_le
-- name    : JardenShami.mk_lim_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:00.250185+00:00
-- url     : https://prove2.me/theorems/2e6598a9-cea2-4ce3-9794-73580d1baa97
-- title:
--   Jarden Shami: mk lim le
-- statement:
--   AUX: not in paper. In a tree of height `μ`, a chain `b` is determined by the function
--   sending `α < μ` to the node of `b` of height `α` (if any); hence `|Lim(T)| ≤ (|T| + 1)^μ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L67-L89
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L67-L89

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.mk_lim_le {T : Type w} [PartialOrder T] [IsTree T] {μ : Cardinal.{w}}
    (hT : height T = μ.ord) : #(Lim T) ≤ (#T + 1) ^ μ := by sorry
