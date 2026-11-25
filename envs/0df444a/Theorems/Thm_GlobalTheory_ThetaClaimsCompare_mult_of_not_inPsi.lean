-- Prove2me | Theorems.Thm_GlobalTheory_ThetaClaimsCompare_mult_of_not_inPsi
-- name    : GlobalTheory.ThetaClaimsCompare.mult_of_not_inPsi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:45.891301+00:00
-- url     : https://prove2.me/theorems/c33b0479-22df-4eda-bac9-2e6851f64595
-- title:
--   Theta Claims Compare: mult of not in Psi
-- statement:
--   The Theta Claims Compare construction uses the mult of not in Psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L229-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L229-L229

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

theorem GlobalTheory.ThetaClaimsCompare.mult_of_not_inPsi {τ : E →+* ℂ} (h : ¬ InPsi H τ) : Dw.mult τ = Dw.q := by sorry
