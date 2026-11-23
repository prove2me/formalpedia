-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_minpoly_eq_cyclotomic_of_isPrimitiveRoot
-- name    : GroundTheory.PAdicHodge.minpoly_eq_cyclotomic_of_isPrimitiveRoot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:26.847399+00:00
-- url     : https://prove2.me/theorems/377823d7-f43b-4470-ae64-b64f515e2c85
-- title:
--   PAdic Hodge: minpoly eq cyclotomic of is Primitive Root
-- statement:
--   The PAdic Hodge construction uses the minpoly eq cyclotomic of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L81-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L81-L127

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

theorem GroundTheory.PAdicHodge.minpoly_eq_cyclotomic_of_isPrimitiveRoot {ζ : PadicAlgCl p} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    minpoly ℚ_[p] ζ = cyclotomic (p ^ (k + 1)) ℚ_[p] := by sorry
