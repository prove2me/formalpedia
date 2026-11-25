-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_isUnitriangular_lastColMat
-- name    : GroundTheory.Automorphic.Reduction.isUnitriangular_lastColMat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:15.508253+00:00
-- url     : https://prove2.me/theorems/25f5fe30-3536-4621-891d-23e06882b0d0
-- title:
--   Reduction: is Unitriangular last Col Mat
-- statement:
--   The Reduction construction uses the is Unitriangular last Col Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L89-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L89-L105

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
variable {R : Type*} [CommRing R] {m : ℕ}

theorem GroundTheory.Automorphic.Reduction.isUnitriangular_lastColMat {A : Matrix (Fin m) (Fin m) R} (hA : IsUnitriangular A)
    (v : Fin m → R) : IsUnitriangular (lastColMat A v) := by sorry
