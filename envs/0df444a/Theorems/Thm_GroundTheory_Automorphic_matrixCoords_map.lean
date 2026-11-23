-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_matrixCoords_map
-- name    : GroundTheory.Automorphic.matrixCoords_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:27.881987+00:00
-- url     : https://prove2.me/theorems/1dff7c12-ea56-4074-b736-5925f26fc95e
-- title:
--   Automorphic: matrix Coords map
-- statement:
--   The Automorphic construction uses the matrix Coords map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L53-L56

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)
variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]
variable {R}
omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.matrixCoords_map (f : R →ₐ[F] S) (g : Matrix ι ι (R ⊗[F] E)) :
    matrixCoords b S (g.map (tensorMap E f)) = f ∘ matrixCoords b R g := by sorry
