-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_toFrac_eq
-- name    : GroundTheory.PAdicHodge.NormTower.Fam.toFrac_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:58.864816+00:00
-- url     : https://prove2.me/theorems/92486c39-02ad-57ef-9fef-1b9895d23a38
-- title:
--   Fam: to Frac eq
-- statement:
--   The Fam construction uses the to Frac eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L292-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L292-L300

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
open GroundTheory.PAdicHodge.NormTower
variable (t : NormTower K Ω p)
open GroundTheory.PAdicHodge.NormTower.Fam
variable {t}

theorem GroundTheory.PAdicHodge.NormTower.Fam.toFrac_eq (x : t.Fam) (m : ℕ) (h : t.value 0 ^ m * nrm K (x.1 0) ≤ 1) :
    toFrac x = IsLocalization.mk' _ (scalePlus x m h) ⟨Plus.unif t ^ m, unif_pow_mem _⟩ := by sorry
