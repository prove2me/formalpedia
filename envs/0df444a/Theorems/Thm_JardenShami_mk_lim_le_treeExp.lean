-- Prove2me | Theorems.Thm_JardenShami_mk_lim_le_treeExp
-- name    : JardenShami.mk_lim_le_treeExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:19.673778+00:00
-- url     : https://prove2.me/theorems/0e59be5f-0303-49bb-b4ba-28eb745f53df
-- title:
--   Jarden Shami: mk lim le tree Exp
-- statement:
--   AUX: not in paper. If `T` has height `μ` and at most `λ` nodes, then `|Lim(T)| ≤ λ^{μ,tr}`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L124-L128
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L124-L128

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.mk_lim_le_treeExp {T : Type w} [PartialOrder T] [IsTree T] {lam μ : Cardinal.{w}}
    (hT : height T = μ.ord) (hcard : #T ≤ lam) : #(Lim T) ≤ treeExp lam μ := by sorry
