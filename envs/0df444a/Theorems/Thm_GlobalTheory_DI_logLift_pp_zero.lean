-- Prove2me | Theorems.Thm_GlobalTheory_DI_logLift_pp_zero
-- name    : GlobalTheory.DI.logLift_pp_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:38.786819+00:00
-- url     : https://prove2.me/theorems/4b26fe8a-94f6-4cc5-b6bf-3408588048b5
-- title:
--   DI: log Lift pp zero
-- statement:
--   The DI construction uses the log Lift pp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogLiftPpZero.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogLiftPpZero.lean#L12-L13

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogLiftPpZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
variable {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K)
  {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (A : Subring K)
omit [Fact p.Prime]

theorem GlobalTheory.DI.logLift_pp_zero (hπ : IsFlatLift p π) : (p : Kt) * p = 0 := by sorry
