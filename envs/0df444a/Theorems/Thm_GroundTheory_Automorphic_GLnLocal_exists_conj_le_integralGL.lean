-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_conj_le_integralGL
-- name    : GroundTheory.Automorphic.GLnLocal.exists_conj_le_integralGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:21.050219+00:00
-- url     : https://prove2.me/theorems/9526656a-9ac6-42a7-8b8f-e4ae4ee2531f
-- title:
--   GLn Local: exists conj le integral GL
-- statement:
--   The GLn Local construction uses the exists conj le integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L378-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L378-L424

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

theorem GroundTheory.Automorphic.GLnLocal.exists_conj_le_integralGL {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) :
    ∃ g : GL (Fin n) F, ∀ h ∈ H, g⁻¹ * h * g ∈ integralGL F n := by sorry
