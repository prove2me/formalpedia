-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum_towerVec_mul
-- name    : GroundTheory.PAdicHodge.normTrace_sum_towerVec_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:52.429692+00:00
-- url     : https://prove2.me/theorems/3cf1b766-b461-41af-9b4c-10a6753e03ff
-- title:
--   PAdic Hodge: norm Trace sum tower Vec mul
-- statement:
--   The PAdic Hodge construction uses the norm Trace sum tower Vec mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L160-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L160-L174

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

theorem GroundTheory.PAdicHodge.normTrace_sum_towerVec_mul {m : ℕ} (hm : stableIndex K ≤ m)
    (c : Fin (relDeg K (stableIndex K)) → PadicAlgCl p) (hc : ∀ i, c i ∈ cycl p m)
    (j : Fin (relDeg K (stableIndex K))) :
    normTrace (cycl p m) ((∑ i, c i * towerVec K i) * towerDualVec K j) =
      c j / (relDeg K (stableIndex K) : PadicAlgCl p) := by sorry
