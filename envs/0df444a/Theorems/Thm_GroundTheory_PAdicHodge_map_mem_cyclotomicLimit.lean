-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_mem_cyclotomicLimit
-- name    : GroundTheory.PAdicHodge.map_mem_cyclotomicLimit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:47.8438+00:00
-- url     : https://prove2.me/theorems/439c88d6-6f5a-414f-908c-86a3ae434c63
-- title:
--   PAdic Hodge: map mem cyclotomic Limit
-- statement:
--   The PAdic Hodge construction uses the map mem cyclotomic Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L275-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L275-L279

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

theorem GroundTheory.PAdicHodge.map_mem_cyclotomicLimit (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    σ x ∈ cyclotomicLimit K := by sorry
