-- Prove2me | Theorems.Thm_GlobalTheory_NabCol_fo_col
-- name    : GlobalTheory.NabCol.fo_col
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:46:35.565807+00:00
-- url     : https://prove2.me/theorems/ba89036a-f970-4356-8367-5551dcd2f48e
-- title:
--   Nab Col: fo col
-- statement:
--   The Nab Col construction uses the fo col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumSupportRename.lean#L175-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumSupportRename.lean#L175-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory GlobalTheory.NabCol
variable {k : Type} [CommRing k] {d n : ℕ}

theorem GlobalTheory.NabCol.fo_col (F : Fin d → PS k 2 d) (hF : ∀ u v, Function.Commute (Dof F u) (Dof F v)) {Λ Ix : Type} [Fintype Λ]
    [Fintype Ix] (e : Λ × Fin n → Ix) (cp : Ix → Fin n) (u : Λ → Fin d → k) (u' : Ix → Fin d → k)
    (hcp : ∀ p, cp (e p) = p.2) (hu : ∀ p, u' (e p) = u p.1) (b : Fin n) (mo : Λ × Fin n →₀ ℕ) (x : PS k 1 d) :
    fo (fun l => colD F (cp l) (u' l) b) Finset.univ.toList (Finsupp.mapDomain e mo) x =
      DmonOf F u (colM mo b) x := by sorry
