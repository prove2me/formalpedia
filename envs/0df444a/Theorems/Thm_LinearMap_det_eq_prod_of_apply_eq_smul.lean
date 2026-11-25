-- Prove2me | Theorems.Thm_LinearMap_det_eq_prod_of_apply_eq_smul
-- name    : LinearMap.det_eq_prod_of_apply_eq_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:44.545257+00:00
-- url     : https://prove2.me/theorems/1e4cfdc5-ea49-410c-850c-c63a49628235
-- title:
--   Linear Map: det eq prod of apply eq smul
-- statement:
--   If a basis `b` consists of eigenvectors of `T`, with `T (b i) = μ i • b i`, then
--   `det T = ∏ᵢ μᵢ`. (The matrix of `T` in the basis `b` is `diagonal μ`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Determinant.lean#L48-L59
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Determinant.lean#L48-L59

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

theorem LinearMap.det_eq_prod_of_apply_eq_smul {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M) (T : M →ₗ[R] M)
    (μ : ι → R) (h : ∀ i, T (b i) = μ i • b i) :
    LinearMap.det T = ∏ i, μ i := by sorry
