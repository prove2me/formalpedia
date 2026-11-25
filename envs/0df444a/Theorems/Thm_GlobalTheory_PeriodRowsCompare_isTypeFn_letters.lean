-- Prove2me | Theorems.Thm_GlobalTheory_PeriodRowsCompare_isTypeFn_letters
-- name    : GlobalTheory.PeriodRowsCompare.isTypeFn_letters
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:16.519261+00:00
-- url     : https://prove2.me/theorems/7ba5caea-6ce8-4090-9df1-3348c96d9029
-- title:
--   Period Rows Compare: is Type Fn letters
-- statement:
--   The Period Rows Compare construction uses the is Type Fn letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ModelBaseTrivModels.lean#L13-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ModelBaseTrivModels.lean#L13-L39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ModelFamilies
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModelBaseTrivModels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodRowsCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem GlobalTheory.PeriodRowsCompare.isTypeFn_letters (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by sorry
