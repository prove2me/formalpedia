-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev_zero
-- name    : GlobalTheory.FormalLog.pderiv_ev_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:42.533081+00:00
-- url     : https://prove2.me/theorems/23b0dd81-7fbb-4d6e-96fd-1014c6aa5ba1
-- title:
--   Formal Log: pderiv ev zero
-- statement:
--   The Formal Log construction uses the pderiv ev zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L47-L49

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
variable (G : FGLaw k d)

theorem GlobalTheory.FormalLog.pderiv_ev_zero {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d)
    (h : ∀ j i, pderiv k v (a j i) = 0) : pderiv k v (ev a f) = 0 := by sorry
