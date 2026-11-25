-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_exists_invariant_of_mem_schwartzBruhat2
-- name    : GroundTheory.Automorphic.GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:44.882598+00:00
-- url     : https://prove2.me/theorems/6a6cfa27-1bab-4240-b043-9597cad702d3
-- title:
--   Godement Section Local: exists invariant of mem schwartz Bruhat2
-- statement:
--   The Godement Section Local construction uses the exists invariant of mem schwartz Bruhat2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L300-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L300-L347

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]

theorem GroundTheory.Automorphic.GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 {Φ : (Fin 2 → F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ N M : ℤ, M ≤ N ∧ (∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) ∧
      ∀ x, Φ x ≠ 0 → x ∈ box F M := by sorry
