-- Prove2me | Theorems.Thm_GlobalTheory_DerivEndo_dof_smul_dir
-- name    : GlobalTheory.DerivEndo.dof_smul_dir
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:33.084502+00:00
-- url     : https://prove2.me/theorems/dcb0c1f9-11e4-4241-969e-def85d6d4956
-- title:
--   Deriv Endo: dof smul dir
-- statement:
--   The Deriv Endo construction uses the dof smul dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvariantDerivAlongEndo.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvariantDerivAlongEndo.lean#L42-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.DerivEndo
open GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.DerivEndo.dof_smul_dir (F : Fin d → PS k 2 d) (c : k) (u : Fin d → k) (g : PS k 1 d) :
    Dof F (c • u) g = C c * Dof F u g := by sorry
