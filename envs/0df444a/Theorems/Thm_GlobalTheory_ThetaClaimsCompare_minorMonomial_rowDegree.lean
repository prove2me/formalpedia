-- Prove2me | Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minorMonomial_rowDegree
-- name    : GlobalTheory.ThetaClaimsCompare.minorMonomial_rowDegree
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:27.728351+00:00
-- url     : https://prove2.me/theorems/5b4d7688-8a77-4f30-961d-703d37b2d30c
-- title:
--   Theta Claims Compare: minor Monomial row Degree
-- statement:
--   The Theta Claims Compare construction uses the minor Monomial row Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L149-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean#L149-L196

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

theorem GlobalTheory.ThetaClaimsCompare.minorMonomial_rowDegree (a : T → ℕ → ℕ) (ha : ∀ σ, Antitone (a σ)) (h0 : ∀ σ, a σ (r σ) = 0) :
    RowDeg r n k a (minorsP r n col k a) := by sorry
