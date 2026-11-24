-- Prove2me | Theorems.Thm_GlobalTheory_MajInv_col_map_eq
-- name    : GlobalTheory.MajInv.col_map_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:20:15.219068+00:00
-- url     : https://prove2.me/theorems/c146c801-3ea5-4619-9874-af40713ce7f2
-- title:
--   Maj Inv: col map eq
-- statement:
--   The Maj Inv construction uses the col map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajLactRmul.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajLactRmul.lean#L19-L22

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
open Matrix
open scoped ComplexConjugate
variable {r : ℕ} (X : Data E r)
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.MajInv.col_map_eq (P : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ) (k : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (P.map τ) k = Data.emb τ (P *ᵥ Pi.single k 1) := by sorry
