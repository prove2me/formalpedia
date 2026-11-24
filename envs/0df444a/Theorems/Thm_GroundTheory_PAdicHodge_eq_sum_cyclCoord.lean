-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_eq_sum_cyclCoord
-- name    : GroundTheory.PAdicHodge.eq_sum_cyclCoord
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:18.86093+00:00
-- url     : https://prove2.me/theorems/1157649d-eeec-4fbb-bd78-03a036f967be
-- title:
--   PAdic Hodge: eq sum cycl Coord
-- statement:
--   The PAdic Hodge construction uses the eq sum cycl Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L471-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L471-L501

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

theorem GroundTheory.PAdicHodge.eq_sum_cyclCoord {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) :
    y = ∑ i ∈ Finset.range p, cyclCoord k η y i * η ^ i := by sorry
