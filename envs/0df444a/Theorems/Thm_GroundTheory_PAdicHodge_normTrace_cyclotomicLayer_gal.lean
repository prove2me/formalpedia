-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cyclotomicLayer_gal
-- name    : GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_gal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:32.832935+00:00
-- url     : https://prove2.me/theorems/8b782d43-f8cf-4aab-8cbd-7b0fa75c122d
-- title:
--   PAdic Hodge: norm Trace cyclotomic Layer gal
-- statement:
--   The PAdic Hodge construction uses the norm Trace cyclotomic Layer gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L290-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L290-L292

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

theorem GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) := by sorry
