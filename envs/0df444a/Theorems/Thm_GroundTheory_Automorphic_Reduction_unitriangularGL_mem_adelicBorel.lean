-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_unitriangularGL_mem_adelicBorel
-- name    : GroundTheory.Automorphic.Reduction.unitriangularGL_mem_adelicBorel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:50.188997+00:00
-- url     : https://prove2.me/theorems/592c6834-2995-4375-b088-d495aa2e6fbf
-- title:
--   Reduction: unitriangular GL mem adelic Borel
-- statement:
--   The Reduction construction uses the unitriangular GL mem adelic Borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L193-L195

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

theorem GroundTheory.Automorphic.Reduction.unitriangularGL_mem_adelicBorel (p : Fin n → Fin n → 𝔸[K]) :
    unitriangularGL n p ∈ adelicBorel := by sorry
