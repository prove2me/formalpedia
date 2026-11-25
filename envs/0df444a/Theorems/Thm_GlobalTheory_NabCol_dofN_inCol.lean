-- Prove2me | Theorems.Thm_GlobalTheory_NabCol_dofN_inCol
-- name    : GlobalTheory.NabCol.dofN_inCol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:35.006116+00:00
-- url     : https://prove2.me/theorems/2da42668-6279-4781-9b6a-6b85a7c64e10
-- title:
--   Nab Col: dof N in Col
-- statement:
--   The Nab Col construction uses the dof N in Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumSupportRename.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumSupportRename.lean#L120-L128

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

theorem GlobalTheory.NabCol.dofN_inCol (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f : PS k 1 d) :
    DofN F b u (inCol b f) = inCol b (Dof F u f) := by sorry
