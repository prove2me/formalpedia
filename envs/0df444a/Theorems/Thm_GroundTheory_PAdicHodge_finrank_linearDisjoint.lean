-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_finrank_linearDisjoint
-- name    : GroundTheory.PAdicHodge.finrank_linearDisjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:14.618806+00:00
-- url     : https://prove2.me/theorems/8586ede8-a888-458b-aab0-43e92fe39f69
-- title:
--   PAdic Hodge: finrank linear Disjoint
-- statement:
--   The PAdic Hodge construction uses the finrank linear Disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L82-L87

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

theorem GroundTheory.PAdicHodge.finrank_linearDisjoint {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) :
    finrank ℚ_[p] (cyclotomicLayer K m) * finrank ℚ_[p] (cycl p n) =
      finrank ℚ_[p] (cyclotomicLayer K n) * finrank ℚ_[p] (cycl p m) := by sorry
