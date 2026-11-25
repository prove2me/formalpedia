-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_val_eq_zero_iff
-- name    : GroundTheory.PAdicHodge.NormTower.Fam.val_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:50.313128+00:00
-- url     : https://prove2.me/theorems/a78b1b21-f677-520d-b852-3ca2896241aa
-- title:
--   Fam: val eq zero iff
-- statement:
--   The Fam construction uses the val eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L252-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L252-L254

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

theorem GroundTheory.PAdicHodge.NormTower.Fam.val_eq_zero_iff (x : t.Fam) (n : ℕ) : x.1 n = 0 ↔ x.1 0 = 0 := by sorry
