-- Prove2me | Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minor_weighted
-- name    : GlobalTheory.ThetaClaimsCompare.minor_weighted
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:47.213578+00:00
-- url     : https://prove2.me/theorems/b7e87f8f-2fc7-4eab-8ff5-767085df971d
-- title:
--   Theta Claims Compare: minor weighted
-- statement:
--   The Theta Claims Compare construction uses the minor weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L122-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L122-L134

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

theorem GlobalTheory.ThetaClaimsCompare.minor_weighted (w : (Σ σ, Fin (r σ)) → ℕ) (σ : T) (s : Fin (r σ)) :
    (minor r n col k σ s).IsWeightedHomogeneous (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
      (∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩) := by sorry
