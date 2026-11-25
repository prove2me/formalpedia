-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Plus_pow_max_max_le_max_pow
-- name    : GroundTheory.PAdicHodge.NormTower.Plus.pow_max_max_le_max_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:51.058802+00:00
-- url     : https://prove2.me/theorems/831835fe-c443-4e6f-bd2a-dc2a3a7ffbba
-- title:
--   Plus: pow max max le max pow
-- statement:
--   The Plus construction uses the pow max max le max pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L185-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean#L185-L192

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

theorem GroundTheory.PAdicHodge.NormTower.Plus.pow_max_max_le_max_pow {a b c : ℝ} (n : ℕ) :
    (max (max a b) c) ^ n ≤ max (max (a ^ n) (b ^ n)) (c ^ n) := by sorry
