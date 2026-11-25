-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_unitriangularGL
-- name    : GroundTheory.Automorphic.Reduction.continuous_unitriangularGL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:08.756616+00:00
-- url     : https://prove2.me/theorems/22440392-43d4-45c2-b041-2675acc76569
-- title:
--   Reduction: continuous unitriangular GL
-- statement:
--   The Reduction construction uses the continuous unitriangular GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L182-L191

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

theorem GroundTheory.Automorphic.Reduction.continuous_unitriangularGL :
    Continuous (unitriangularGL n : (Fin n → Fin n → 𝔸[K]) → AdelicGLn.AdelicGL K n) := by sorry
