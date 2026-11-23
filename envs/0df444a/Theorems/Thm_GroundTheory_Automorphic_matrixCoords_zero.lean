-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
-- name    : GroundTheory.Automorphic.matrixCoords_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:36.402113+00:00
-- url     : https://prove2.me/theorems/764443b8-46c1-4728-9298-824c67bca3b5
-- title:
--   Automorphic: matrix Coords zero
-- statement:
--   The Automorphic construction uses the matrix Coords zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L33-L36

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

theorem GroundTheory.Automorphic.matrixCoords_zero : matrixCoords b R (0 : Matrix ι ι (R ⊗[F] E)) = 0 := by sorry
