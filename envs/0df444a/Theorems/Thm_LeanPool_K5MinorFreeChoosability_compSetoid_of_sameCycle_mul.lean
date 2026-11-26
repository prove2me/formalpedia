-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_of_sameCycle_mul
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_of_sameCycle_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:49.763566+00:00
-- url     : https://prove2.me/theorems/a292c8fd-3364-5479-9b43-66ae4258e3f9
-- title:
--   K5 Minor Free Choosability: comp Setoid of same Cycle mul
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid of same Cycle mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L80-L83
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L80-L83

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.compSetoid_of_sameCycle_mul {σ α : Perm D} {a b : D} (h : SameCycle (σ * α) a b) :
    compSetoid σ α a b := by sorry
