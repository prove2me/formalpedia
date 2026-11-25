-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_NormTower_IsFam_nrm_eq
-- name    : GroundTheory.PAdicHodge.NormTower.IsFam.nrm_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:21:15.179803+00:00
-- url     : https://prove2.me/theorems/38a7fdee-c7f7-5a76-8068-b857dbd09fcf
-- title:
--   Is Fam: nrm eq
-- statement:
--   The Is Fam construction uses the nrm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsRing.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsRing.lean#L164-L166

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
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
open GroundTheory.PAdicHodge.NormTower
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
  (t : NormTower K Ω p)
variable {t}

theorem GroundTheory.PAdicHodge.NormTower.IsFam.nrm_eq {z : ℕ → Ω} (hz : t.IsFam z) (i j : ℕ) :
    nrm K (z i) = nrm K (z (i + j)) ^ t.D i j := by sorry
