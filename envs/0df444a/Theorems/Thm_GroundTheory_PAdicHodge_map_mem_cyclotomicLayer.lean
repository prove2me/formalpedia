-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_mem_cyclotomicLayer
-- name    : GroundTheory.PAdicHodge.map_mem_cyclotomicLayer
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:01.206721+00:00
-- url     : https://prove2.me/theorems/d8769660-fe71-4282-8579-5e32c173a823
-- title:
--   PAdic Hodge: map mem cyclotomic Layer
-- statement:
--   The PAdic Hodge construction uses the map mem cyclotomic Layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L268-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L268-L272

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

theorem GroundTheory.PAdicHodge.map_mem_cyclotomicLayer (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cyclotomicLayer K n) :
    σ x ∈ cyclotomicLayer K n := by sorry
