-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_IsUnitriangular_mul
-- name    : GroundTheory.Automorphic.Reduction.IsUnitriangular.mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:27:16.216926+00:00
-- url     : https://prove2.me/theorems/435469b6-0275-4e28-997b-2b5dd7f1ed48
-- title:
--   Is Unitriangular: mul
-- statement:
--   The Is Unitriangular construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L47-L56

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
variable {R : Type*} [CommRing R] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.IsUnitriangular.mul {M N : Matrix (Fin n) (Fin n) R} (hM : IsUnitriangular M)
    (hN : IsUnitriangular N) : IsUnitriangular (M * N) := by sorry
