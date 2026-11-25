-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cyclotomicLayer_eq_of_mem
-- name    : GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_eq_of_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:07.660888+00:00
-- url     : https://prove2.me/theorems/5110c329-b885-45dc-8318-43e4553ddb32
-- title:
--   PAdic Hodge: norm Trace cyclotomic Layer eq of mem
-- statement:
--   The PAdic Hodge construction uses the norm Trace cyclotomic Layer eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L96-L101

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

theorem GroundTheory.PAdicHodge.normTrace_cyclotomicLayer_eq_of_mem {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m)
    {a : PadicAlgCl p} (ha : a ∈ cycl p m) :
    normTrace (cyclotomicLayer K n) a = normTrace (cycl p n) a := by sorry
