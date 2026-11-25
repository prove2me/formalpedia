-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_diagUnits_mem_adelicBorel
-- name    : GroundTheory.Automorphic.Reduction.diagUnits_mem_adelicBorel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:23:35.652967+00:00
-- url     : https://prove2.me/theorems/24ff758c-b20b-5721-86a8-ca1a55a6ffae
-- title:
--   Reduction: diag Units mem adelic Borel
-- statement:
--   The Reduction construction uses the diag Units mem adelic Borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L172-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L172-L175

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

theorem GroundTheory.Automorphic.Reduction.diagUnits_mem_adelicBorel (d : Fin n → IdeleGroup K) :
    diagUnits n d ∈ adelicBorel := by sorry
