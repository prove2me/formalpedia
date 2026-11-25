-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_diagUnits
-- name    : GroundTheory.Automorphic.Reduction.continuous_diagUnits
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:25:34.254373+00:00
-- url     : https://prove2.me/theorems/3291ffb9-31c8-4c51-8709-08861cf24bc3
-- title:
--   Reduction: continuous diag Units
-- statement:
--   The Reduction construction uses the continuous diag Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L156-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L156-L163

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

theorem GroundTheory.Automorphic.Reduction.continuous_diagUnits :
    Continuous (diagUnits n : (Fin n → IdeleGroup K) → AdelicGLn.AdelicGL K n) := by sorry
