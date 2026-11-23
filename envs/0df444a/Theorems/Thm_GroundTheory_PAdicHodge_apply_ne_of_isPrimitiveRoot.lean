-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_apply_ne_of_isPrimitiveRoot
-- name    : GroundTheory.PAdicHodge.apply_ne_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:38.433808+00:00
-- url     : https://prove2.me/theorems/7d077b04-8710-47be-a224-1b81aa94f2cc
-- title:
--   PAdic Hodge: apply ne of is Primitive Root
-- statement:
--   The PAdic Hodge construction uses the apply ne of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L559-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L559-L586

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

theorem GroundTheory.PAdicHodge.apply_ne_of_isPrimitiveRoot {k : ℕ} (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (hτη : τ η ≠ η) {η' : PadicAlgCl p} (hη' : IsPrimitiveRoot η' (p ^ (k + 1))) : τ η' ≠ η' := by sorry
