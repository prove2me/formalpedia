-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_IsUnitriangular_eq_unitriangular
-- name    : GroundTheory.Automorphic.Reduction.IsUnitriangular.eq_unitriangular
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:34.225231+00:00
-- url     : https://prove2.me/theorems/9a83a864-f44a-4287-8ea2-201c4ed51583
-- title:
--   Is Unitriangular: eq unitriangular
-- statement:
--   The Is Unitriangular construction uses the eq unitriangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L33-L40

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

theorem GroundTheory.Automorphic.Reduction.IsUnitriangular.eq_unitriangular {M : Matrix (Fin n) (Fin n) R} (hM : IsUnitriangular M) :
    M = unitriangular fun i j => M i j := by sorry
