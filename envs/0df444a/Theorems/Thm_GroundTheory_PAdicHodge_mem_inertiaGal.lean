-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_inertiaGal
-- name    : GroundTheory.PAdicHodge.mem_inertiaGal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:00.048619+00:00
-- url     : https://prove2.me/theorems/40dc2ff8-672d-4e05-b60d-3cefc218e55b
-- title:
--   PAdic Hodge: mem inertia Gal
-- statement:
--   The PAdic Hodge construction uses the mem inertia Gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharClosure.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharClosure.lean#L32-L33

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField
variable {p : ℕ} [hp : Fact p.Prime]

theorem GroundTheory.PAdicHodge.mem_inertiaGal {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {σ : Gal(PadicAlgCl p/K)} :
    σ ∈ inertiaGal K ↔ ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1 := by sorry
