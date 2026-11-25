-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_coe_diagUnits
-- name    : GroundTheory.Automorphic.Reduction.coe_diagUnits
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:25:30.900739+00:00
-- url     : https://prove2.me/theorems/2dd9f015-bb8e-4cc1-962b-08f59aedb2f2
-- title:
--   Reduction: coe diag Units
-- statement:
--   The Reduction construction uses the coe diag Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L153-L154

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
variable (n : ℕ)

theorem GroundTheory.Automorphic.Reduction.coe_diagUnits {R : Type*} [CommRing R] (d : Fin n → Rˣ) :
    ((diagUnits n d : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal fun i => (d i : R) := by sorry

attribute [defeq] GroundTheory.Automorphic.Reduction.coe_diagUnits
