-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cyclotomicLayer_map
-- name    : GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:21.932807+00:00
-- url     : https://prove2.me/theorems/476fb75b-4074-46c9-b514-a158eff14870
-- title:
--   PAdic Hodge: norm Trace cyclotomic Layer map
-- statement:
--   The PAdic Hodge construction uses the norm Trace cyclotomic Layer map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L283-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L283-L286

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
omit [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) := by sorry
