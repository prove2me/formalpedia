-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_adjoin_sub_one_eq_cycl
-- name    : GroundTheory.PAdicHodge.adjoin_sub_one_eq_cycl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:20.535824+00:00
-- url     : https://prove2.me/theorems/9d30d6f0-bfd6-476b-91e6-64aa333048bf
-- title:
--   PAdic Hodge: adjoin sub one eq cycl
-- statement:
--   The PAdic Hodge construction uses the adjoin sub one eq cycl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L242-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L242-L250

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

theorem GroundTheory.PAdicHodge.adjoin_sub_one_eq_cycl {ζ : PadicAlgCl p} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ℚ_[p]⟮ζ - 1⟯ = cycl p n := by sorry
