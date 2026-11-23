-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowDeriv_apply
-- name    : GroundTheory.Automorphic.HarishChandra.rowDeriv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:34.413418+00:00
-- url     : https://prove2.me/theorems/0339366d-32cd-4c67-9366-88d36d7d6334
-- title:
--   Harish Chandra: row Deriv apply
-- statement:
--   The Harish Chandra construction uses the row Deriv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L85-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L85-L100

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.rowDeriv_apply (i j : Fin n) (f : Poly n) : rowDeriv i j f = rowOp i j f := by sorry
