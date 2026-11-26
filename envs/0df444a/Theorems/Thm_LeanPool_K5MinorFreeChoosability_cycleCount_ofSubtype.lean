-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_ofSubtype
-- name    : LeanPool.K5MinorFreeChoosability.cycleCount_ofSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:29.541797+00:00
-- url     : https://prove2.me/theorems/23bc0ceb-3fb3-5192-a61a-535ceb40c318
-- title:
--   K5 Minor Free Choosability: cycle Count of Subtype
-- statement:
--   The K5 Minor Free Choosability construction uses the cycle Count of Subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L305-L311
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L305-L311

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable (p : D → Prop) [DecidablePred p]

theorem LeanPool.K5MinorFreeChoosability.cycleCount_ofSubtype [Finite D] (π : Perm (Subtype p)) :
    cycleCount (ofSubtype π) = cycleCount π + Nat.card {x // ¬ p x} := by sorry
