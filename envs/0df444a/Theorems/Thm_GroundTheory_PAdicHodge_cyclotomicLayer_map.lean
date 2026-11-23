-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_map
-- name    : GroundTheory.PAdicHodge.cyclotomicLayer_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:01.096139+00:00
-- url     : https://prove2.me/theorems/ce1ddc40-0ebf-416e-b610-09f2764862b5
-- title:
--   PAdic Hodge: cyclotomic Layer map
-- statement:
--   The PAdic Hodge construction uses the cyclotomic Layer map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L253-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L253-L265

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

theorem GroundTheory.PAdicHodge.cyclotomicLayer_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : ∀ x ∈ K, σ x = x)
    (n : ℕ) :
    (cyclotomicLayer K n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cyclotomicLayer K n := by sorry
