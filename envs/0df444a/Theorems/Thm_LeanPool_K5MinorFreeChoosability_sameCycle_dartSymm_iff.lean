-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_dartSymm_iff
-- name    : LeanPool.K5MinorFreeChoosability.sameCycle_dartSymm_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:09.36058+00:00
-- url     : https://prove2.me/theorems/ed407fee-a890-4574-b7e9-86f053872fff
-- title:
--   K5 Minor Free Choosability: same Cycle dart Symm iff
-- statement:
--   The K5 Minor Free Choosability construction uses the same Cycle dart Symm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L84-L96
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L84-L96

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)

theorem LeanPool.K5MinorFreeChoosability.sameCycle_dartSymm_iff {d e : G.Dart} :
    SameCycle (dartSymm G) d e ↔ e = d ∨ e = d.symm := by sorry
