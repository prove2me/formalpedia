-- Prove2me | Theorems.Thm_GlobalTheory_ChartTransN_dofN_transF
-- name    : GlobalTheory.ChartTransN.dofN_transF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:23.579256+00:00
-- url     : https://prove2.me/theorems/2e9c7d4b-b10e-57a4-aaf4-9d8d88351c4b
-- title:
--   Chart Trans N: dof N trans F
-- statement:
--   The Chart Trans N construction uses the dof N trans F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/InvariantPolyOperatorCopiesTransportedLaw.lean#L58-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/InvariantPolyOperatorCopiesTransportedLaw.lean#L58-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantPolyOperatorCopiesTransportedLaw
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt

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
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol
open GlobalTheory GlobalTheory.ChartTransN
variable {k : Type} [CommRing k] {d n : ℕ}

theorem GlobalTheory.ChartTransN.dofN_transF (G : FGLaw k d) (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (b : Fin n) (u : Fin d → k)
    (g : PS k n d) :
    DofN (transF G.F φ φi) b u (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
      ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (DofN G.F b ((dLin φ).mulVec u) g) := by sorry
