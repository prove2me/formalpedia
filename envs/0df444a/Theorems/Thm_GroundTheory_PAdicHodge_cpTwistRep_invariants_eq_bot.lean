-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cpTwistRep_invariants_eq_bot
-- name    : GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:10:09.018975+00:00
-- url     : https://prove2.me/theorems/f7c2ecc9-622f-5683-8c70-6f0e3b46b20b
-- title:
--   PAdic Hodge: cp Twist Rep invariants eq bot
-- statement:
--   The PAdic Hodge construction uses the cp Twist Rep invariants eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L296-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L296-L300

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
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
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot {j : ℤ} (hj : j ≠ 0) : (cpTwistRep K j).invariants = ⊥ := by sorry
