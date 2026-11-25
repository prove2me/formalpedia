-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclCoord_apply
-- name    : GroundTheory.PAdicHodge.cyclCoord_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:43.3958+00:00
-- url     : https://prove2.me/theorems/1544f2ab-d462-4431-9ab4-517aeb34ddbb
-- title:
--   PAdic Hodge: cycl Coord apply
-- statement:
--   The PAdic Hodge construction uses the cycl Coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L511-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L511-L524

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

theorem GroundTheory.PAdicHodge.cyclCoord_apply {k : ℕ} (hk : 1 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η ε : PadicAlgCl p} (hεp : ε ^ p = 1) (hτη : τ η = ε * η)
    (y : PadicAlgCl p) {i : ℕ} (hi : i ≤ p ^ (k + 1)) :
    cyclCoord k η (τ y) i = ε ^ i * cyclCoord k η y i := by sorry
