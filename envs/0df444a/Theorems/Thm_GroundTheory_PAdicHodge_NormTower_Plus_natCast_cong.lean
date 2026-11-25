-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Plus_natCast_cong
-- name    : GroundTheory.PAdicHodge.NormTower.Plus.natCast_cong
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:04.02151+00:00
-- url     : https://prove2.me/theorems/89582b45-7670-4201-b9e1-b0caf779a1ab
-- title:
--   Plus: nat Cast cong
-- statement:
--   The Plus construction uses the nat Cast cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L100-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L100-L110

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
open GroundTheory.PAdicHodge.NormTower.Plus
variable {t}

theorem GroundTheory.PAdicHodge.NormTower.Plus.natCast_cong (m n : ℕ) : nrm K (((m : ℕ) : t.Plus).1 n - (m : Ω)) ≤ t.ρ := by sorry
