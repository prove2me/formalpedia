-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_finrank_cycl
-- name    : GroundTheory.PAdicHodge.finrank_cycl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:42.004815+00:00
-- url     : https://prove2.me/theorems/5e8ccd11-ebe3-41b9-9ab7-4835b865f451
-- title:
--   PAdic Hodge: finrank cycl
-- statement:
--   The PAdic Hodge construction uses the finrank cycl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L137-L146

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

theorem GroundTheory.PAdicHodge.finrank_cycl (n : ℕ) : finrank ℚ_[p] (cycl p n) = Nat.totient (p ^ n) := by sorry
