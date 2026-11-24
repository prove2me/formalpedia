-- Prove2me | Theorems.Thm_GlobalTheory_FormalCocycle_exists_coboundary_of_symm_cocycle
-- name    : GlobalTheory.FormalCocycle.exists_coboundary_of_symm_cocycle
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:34.13315+00:00
-- url     : https://prove2.me/theorems/dc90396f-f5d9-4389-833a-c30cd5412de8
-- title:
--   Formal Cocycle: exists coboundary of symm cocycle
-- statement:
--   The Formal Cocycle construction uses the exists coboundary of symm cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L219-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L219-L322

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum
open GlobalTheory GlobalTheory.FormalCocycle

theorem GlobalTheory.FormalCocycle.exists_coboundary_of_symm_cocycle :
    LogSt → (∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) → IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h) := by sorry
