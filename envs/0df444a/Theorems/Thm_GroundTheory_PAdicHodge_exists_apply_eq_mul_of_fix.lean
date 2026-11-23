-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_apply_eq_mul_of_fix
-- name    : GroundTheory.PAdicHodge.exists_apply_eq_mul_of_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:48.47081+00:00
-- url     : https://prove2.me/theorems/fee1cceb-4a76-4d4d-a8bd-7c502aeaa28c
-- title:
--   PAdic Hodge: exists apply eq mul of fix
-- statement:
--   The PAdic Hodge construction uses the exists apply eq mul of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L425-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L425-L432

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
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
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.exists_apply_eq_mul_of_fix {k : ℕ} (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1))) :
    ∃ ε : PadicAlgCl p, ε ^ p = 1 ∧ τ η = ε * η := by sorry
