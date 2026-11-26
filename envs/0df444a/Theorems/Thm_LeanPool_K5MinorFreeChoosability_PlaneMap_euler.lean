-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_PlaneMap_euler
-- name    : LeanPool.K5MinorFreeChoosability.PlaneMap.euler
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:21:00.353801+00:00
-- url     : https://prove2.me/theorems/ff71e0f6-c53e-43c3-a174-edfa36ae993b
-- title:
--   Plane Map: euler
-- statement:
--   **Euler's formula** for a plane map: `V - E + F = 2 K`, where `V` counts rotation cycles
--   (vertices with an edge), `E` edges, `F` faces and `K` components.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L135-L143
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L135-L143

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)

theorem LeanPool.K5MinorFreeChoosability.PlaneMap.euler [Finite V] {G : SimpleGraph V} (M : PlaneMap G) :
    (cycleCount M.rot : ℤ) - Nat.card G.edgeSet + M.numFaces =
      2 * numComponents M.rot (dartSymm G) := by sorry
