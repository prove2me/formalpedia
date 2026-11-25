-- Prove2me | Theorems.Thm_LinearMap_det_adjoint
-- name    : LinearMap.det_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:05:52.648275+00:00
-- url     : https://prove2.me/theorems/9e66b7a5-93c0-4cdd-9f3f-fe7565a28257
-- title:
--   Linear Map: det adjoint
-- statement:
--   **`det T* = conj (det T)`.** In an orthonormal basis the matrix of the
--   adjoint is the conjugate transpose, and `det Aᴴ = conj (det A)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Determinant.lean#L38-L42
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Determinant.lean#L38-L42

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Determinant
public import Definitions.Def_BasicResults_Determinant
set_option autoImplicit true
@[expose] public section
public section
open LinearMap
open scoped ComplexConjugate
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

theorem LinearMap.det_adjoint (T : E →ₗ[𝕜] E) :
    LinearMap.det (adjoint T) = conj (LinearMap.det T) := by sorry
