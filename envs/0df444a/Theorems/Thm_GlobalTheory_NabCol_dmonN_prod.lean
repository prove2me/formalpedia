-- Prove2me | Theorems.Thm_GlobalTheory_NabCol_dmonN_prod
-- name    : GlobalTheory.NabCol.dmonN_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:17.543101+00:00
-- url     : https://prove2.me/theorems/12f41ece-66e1-4fad-b9c6-57aeef2b43dd
-- title:
--   Nab Col: dmon N prod
-- statement:
--   The Nab Col construction uses the dmon N prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumSupportRename.lean#L166-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumSupportRename.lean#L166-L173

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

theorem GlobalTheory.NabCol.dmonN_prod (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ)
    (g : Fin n → PS k 1 d) :
    DmonN F cp u m (∏ b, inCol b (g b)) =
      ∏ b, inCol b (fo (fun l => colD F (cp l) (u l) b) Finset.univ.toList m (g b)) := by sorry
