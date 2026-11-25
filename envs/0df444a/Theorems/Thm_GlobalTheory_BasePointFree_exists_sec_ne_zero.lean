-- Prove2me | Theorems.Thm_GlobalTheory_BasePointFree_exists_sec_ne_zero
-- name    : GlobalTheory.BasePointFree.exists_sec_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:46.162799+00:00
-- url     : https://prove2.me/theorems/bd98890e-1cad-4259-a025-017e68152d87
-- title:
--   Base Point Free: exists sec ne zero
-- statement:
--   The Base Point Free construction uses the exists sec ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNeZeroPair.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNeZeroPair.lean#L52-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.BasePointFree

theorem GlobalTheory.BasePointFree.exists_sec_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ), s ∈ X.Sec 1 1 → s ≠ 0 → ∀ q : ℕ, 2 ≤ q → ∀ v : Fin 1 → Vsp X.dim, ∃ F ∈ X.Sec q 1, F v ≠ 0 := by sorry
