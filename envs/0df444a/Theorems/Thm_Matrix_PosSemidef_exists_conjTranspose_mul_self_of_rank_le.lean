-- Prove2me | Theorems.Thm_Matrix_PosSemidef_exists_conjTranspose_mul_self_of_rank_le
-- name    : Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:06.861312+00:00
-- url     : https://prove2.me/theorems/d127b5d1-8513-4b2f-8d6b-8493e12ed840
-- title:
--   Pos Semidef: exists conj Transpose mul self of rank le
-- statement:
--   A positive semidefinite matrix `G` with `G.rank ≤ k` factors as `Mᴴ * M` for
--   some matrix `M : Matrix (Fin k) (Fin n) ℝ`. This rank-controlled Cholesky-type
--   factorization realizes `G` in ambient dimension `k` and uses only `G.rank` active
--   directions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/SchoenbergHard.lean#L141-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/SchoenbergHard.lean#L141-L174

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_LeanPool_DistanceGeometry_SchoenbergHard
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open scoped RealInnerProductSpace
open Matrix
variable {n k : ℕ}
open Matrix.PosSemidef
variable {G : Matrix (Fin n) (Fin n) ℝ}

theorem Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le (hG : G.PosSemidef) (hrank : G.rank ≤ k) :
    ∃ M : Matrix (Fin k) (Fin n) ℝ, Mᴴ * M = G := by sorry
