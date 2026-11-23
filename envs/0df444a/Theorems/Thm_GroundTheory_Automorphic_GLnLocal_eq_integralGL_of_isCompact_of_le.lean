-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eq_integralGL_of_isCompact_of_le
-- name    : GroundTheory.Automorphic.GLnLocal.eq_integralGL_of_isCompact_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:08.358345+00:00
-- url     : https://prove2.me/theorems/82178c9c-b6c2-45fc-9e13-b35607c659fd
-- title:
--   GLn Local: eq integral GL of is Compact of le
-- statement:
--   The GLn Local construction uses the eq integral GL of is Compact of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L450-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L450-L457

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.eq_integralGL_of_isCompact_of_le {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) (hle : integralGL F n ≤ H) :
    H = integralGL F n := by sorry
