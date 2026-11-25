-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le_mul
-- name    : GroundTheory.PAdicHodge.NormTower.nrm_N_sub_N_le_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:36.988477+00:00
-- url     : https://prove2.me/theorems/b9b490f2-214a-4512-a3d8-250b080f8975
-- title:
--   Norm Tower: nrm N sub N le mul
-- statement:
--   The Norm Tower construction uses the nrm N sub N le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L470-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L470-L565

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
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
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
open GroundTheory.PAdicHodge.NormTower
variable {K Ω p} (t : NormTower K Ω p)

theorem GroundTheory.PAdicHodge.NormTower.nrm_N_sub_N_le_mul (n : ℕ) (hk : t.k n ≠ 0) {a b : Ω} (ha : a ∈ t.E (n + 1))
    (hb : b ∈ t.E (n + 1)) (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) {s : ℝ} (hs : s ≤ t.ρ)
    (hab : nrm K (a - b) ≤ s) : nrm K (t.N n a - t.N n b) ≤ t.ρ * s := by sorry
