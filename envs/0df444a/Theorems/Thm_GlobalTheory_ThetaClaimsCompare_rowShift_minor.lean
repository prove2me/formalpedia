-- Prove2me | Theorems.Thm_GlobalTheory_ThetaClaimsCompare_rowShift_minor
-- name    : GlobalTheory.ThetaClaimsCompare.rowShift_minor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:44.469703+00:00
-- url     : https://prove2.me/theorems/068a91c7-6869-4e6b-a6f5-dc464ef094f1
-- title:
--   Theta Claims Compare: row Shift minor
-- statement:
--   The Theta Claims Compare construction uses the row Shift minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L80-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L80-L116

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
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)

theorem GlobalTheory.ThetaClaimsCompare.rowShift_minor (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) (σ' : T) (s : Fin (r σ')) :
    rowShift r n k σ i i' t (minor r n col k σ' s) = minor r n col k σ' s := by sorry
