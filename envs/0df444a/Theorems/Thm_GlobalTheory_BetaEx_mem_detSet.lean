-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_mem_detSet
-- name    : GlobalTheory.BetaEx.mem_detSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:44.504166+00:00
-- url     : https://prove2.me/theorems/5c704f1f-3b1f-4f2a-a9dd-6a566d817e8d
-- title:
--   Beta Ex: mem det Set
-- statement:
--   The Beta Ex construction uses the mem det Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L13-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
omit [NumberField E]

theorem GlobalTheory.BetaEx.mem_detSet (M : Submodule (𝓞 E) (Fin n → E)) (d : E) :
    d ∈ detSet M ↔ ∃ v : Matrix (Fin n) (Fin n) E, (∀ i, v i ∈ M) ∧ d = v.det := by sorry
