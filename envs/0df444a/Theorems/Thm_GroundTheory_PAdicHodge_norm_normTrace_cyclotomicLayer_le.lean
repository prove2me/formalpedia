-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_normTrace_cyclotomicLayer_le
-- name    : GroundTheory.PAdicHodge.norm_normTrace_cyclotomicLayer_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:43.931516+00:00
-- url     : https://prove2.me/theorems/b6936c49-3ead-4bd3-8d8a-29569600f800
-- title:
--   PAdic Hodge: norm norm Trace cyclotomic Layer le
-- statement:
--   The PAdic Hodge construction uses the norm norm Trace cyclotomic Layer le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L224-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L224-L249

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.PAdicHodge.norm_normTrace_cyclotomicLayer_le {cF : ℝ} (hcF : 0 ≤ cF)
    (hF : ∀ n m : ℕ, stableIndex K ≤ n → n ≤ m → ∀ x ∈ cycl p m,
      ‖normTrace (cycl p n) x‖ ≤ cF * ‖x‖)
    {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) :
    ‖normTrace (cyclotomicLayer K n) y‖ ≤
      cF * (∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖) * ‖y‖ := by sorry
