-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_diagonal_diagUnits
-- name    : GroundTheory.Automorphic.Reduction.diagonal_diagUnits
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:40.451821+00:00
-- url     : https://prove2.me/theorems/8489bbd2-da0f-4fd9-87f3-761b0d1a4e1b
-- title:
--   Reduction: diagonal diag Units
-- statement:
--   The Reduction construction uses the diagonal diag Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L165-L170

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

theorem GroundTheory.Automorphic.Reduction.diagonal_diagUnits (c : Fin n → Kˣ) :
    AdelicGLn.diagonal K n (diagUnits n c) =
      diagUnits n (fun i => IdeleGroup.diagonal K (c i)) := by sorry
