-- Prove2me | Theorems.Thm_GlobalTheory_Up_Definite_mem_dom
-- name    : GlobalTheory.Up.Definite.mem_dom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:08.3358+00:00
-- url     : https://prove2.me/theorems/f769a618-a451-452e-92e7-019d66cf37eb
-- title:
--   Definite: mem dom
-- statement:
--   The Definite construction uses the mem dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SingleMemIntVec.lean#L182-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SingleMemIntVec.lean#L182-L199

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.Definite
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Up.Definite.mem_dom (x : Frame (data E r).Ψ r) : x ∈ (data E r).dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by sorry
