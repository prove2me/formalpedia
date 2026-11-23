-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_matrixCoords_apply
-- name    : GroundTheory.Automorphic.matrixCoords_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:39.18348+00:00
-- url     : https://prove2.me/theorems/9a1996b5-bc77-4b93-86d7-2b98c5deb636
-- title:
--   Automorphic: matrix Coords apply
-- statement:
--   The Automorphic construction uses the matrix Coords apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L28-L29

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
omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.matrixCoords_apply (g : Matrix ι ι (R ⊗[F] E)) (i j : ι) (k : κ) :
    matrixCoords b R g (i, j, k) = (Algebra.TensorProduct.basis R b).repr (g i j) k := by sorry
