-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_eq_sum_shells
-- name    : GroundTheory.Automorphic.GodementSectionLocal.eq_sum_shells
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:31.15044+00:00
-- url     : https://prove2.me/theorems/98e465ec-ed9d-54b2-b0be-659049fd22d0
-- title:
--   Godement Section Local: eq sum shells
-- statement:
--   The Godement Section Local construction uses the eq sum shells property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L451-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L451-L501

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

theorem GroundTheory.Automorphic.GodementSectionLocal.eq_sum_shells {Φ : (Fin 2 → F) → ℂ} {N M : ℤ} (hMN : M ≤ N)
    (hinv : ∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) (hsupp : ∀ x, Φ x ≠ 0 → x ∈ box F M) :
    Φ = (∑ m ∈ Finset.Ico M N, (shellAt F m).indicator Φ) + Φ 0 • boxInd F N := by sorry
