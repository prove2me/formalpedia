-- Prove2me | Theorems.Thm_GlobalTheory_QuadNormBase_norm_of_basis
-- name    : GlobalTheory.QuadNormBase.norm_of_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:19.087227+00:00
-- url     : https://prove2.me/theorems/485a738f-373d-4e49-b9b4-441a3e1033c7
-- title:
--   Quad Norm Base: norm of basis
-- statement:
--   The Quad Norm Base construction uses the norm of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticExtNormFormOverAlgebra.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticExtNormFormOverAlgebra.lean#L8-L19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadNormBase

theorem GlobalTheory.QuadNormBase.norm_of_basis {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (B : Module.Basis (Fin 2) R A) (d : R) (h0 : B 0 = 1) (h1 : B 1 * B 1 = d • B 0) (x y : R) :
    Algebra.norm R (x • B 0 + y • B 1) = x ^ 2 - d * y ^ 2 := by sorry
