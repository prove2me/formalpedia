-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
-- name    : LeanPool.K5MinorFreeChoosability.dartSymm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:08.201812+00:00
-- url     : https://prove2.me/theorems/fdfc5e63-8bad-443b-bc66-80f0f538bda5
-- title:
--   K5 Minor Free Choosability: dart Symm apply
-- statement:
--   The K5 Minor Free Choosability construction uses the dart Symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L48-L48
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L48-L48

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)

theorem LeanPool.K5MinorFreeChoosability.dartSymm_apply (d : G.Dart) : dartSymm G d = d.symm := by sorry

attribute [defeq] LeanPool.K5MinorFreeChoosability.dartSymm_apply
