-- Prove2me | Theorems.Thm_GlobalTheory_ThetaClaimsCompare_exists_harmA_ne_zero
-- name    : GlobalTheory.ThetaClaimsCompare.exists_harmA_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:09.875888+00:00
-- url     : https://prove2.me/theorems/15f52be9-c757-55b6-acd7-ce3f59e69c28
-- title:
--   Theta Claims Compare: exists harm A ne zero
-- statement:
--   The Theta Claims Compare construction uses the exists harm A ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L260-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L260-L285

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
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
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem GlobalTheory.ThetaClaimsCompare.exists_harmA_ne_zero {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : RowsDominant Dw a) (hn : Dw.p + Dw.q ≤ n) :
    ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0 := by sorry
