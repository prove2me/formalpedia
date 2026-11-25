-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_tateTrace_gal
-- name    : GroundTheory.PAdicHodge.tateTrace_gal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:58.879617+00:00
-- url     : https://prove2.me/theorems/d22fde04-f528-41bf-9fb8-6df36ada6dc1
-- title:
--   PAdic Hodge: tate Trace gal
-- statement:
--   The PAdic Hodge construction uses the tate Trace gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L33-L35

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
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
open IntermediateField Module Set
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.PAdicHodge.tateTrace_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    tateTrace K n (σ y) = σ (tateTrace K n y) := by sorry
