-- Prove2me | Theorems.Thm_GlobalTheory_MajInv_exists_colP_rmul_eq_sum
-- name    : GlobalTheory.MajInv.exists_colP_rmul_eq_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:22:14.478901+00:00
-- url     : https://prove2.me/theorems/a11e3363-5e32-4244-9d85-5b2fda917375
-- title:
--   Maj Inv: exists col P rmul eq sum
-- statement:
--   The Maj Inv construction uses the exists col P rmul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajLactRmul.lean#L54-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajLactRmul.lean#L54-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.MajInv
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MajInv.exists_colP_rmul_eq_sum {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    ∃ L : Fin X.p0 → ℂ, X.colP (rmul x b) τ a = ∑ c, L c • X.colP x τ c := by sorry
