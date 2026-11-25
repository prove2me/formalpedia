-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_shellPiece_mem
-- name    : GroundTheory.Automorphic.GodementSectionLocal.shellPiece_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:37.663337+00:00
-- url     : https://prove2.me/theorems/be824430-ffc7-5a08-bf67-9080e7f5c509
-- title:
--   Godement Section Local: shell Piece mem
-- statement:
--   The Godement Section Local construction uses the shell Piece mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L422-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L422-L427

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

theorem GroundTheory.Automorphic.GodementSectionLocal.shellPiece_mem {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (m : ℤ) :
    shellPiece Φ m ∈ schwartzBruhat2 F := by sorry
