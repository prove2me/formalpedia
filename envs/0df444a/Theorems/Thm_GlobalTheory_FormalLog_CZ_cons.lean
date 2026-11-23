-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_CZ_cons
-- name    : GlobalTheory.FormalLog.CZ.cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:25.980942+00:00
-- url     : https://prove2.me/theorems/d54afabf-a5ee-4367-a68c-da24d7896750
-- title:
--   CZ: cons
-- statement:
--   The CZ construction uses the cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L22-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.FormalLog.CZ.cons {m n : ℕ} {p : Pt k n d} {a : Fin m → Pt k n d} (hp : ∀ i, constantCoeff (p i) = 0) (ha : CZ a) :
    CZ (Matrix.vecCons p a) := by sorry
