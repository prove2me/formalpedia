-- Prove2me | Theorems.Thm_GlobalTheory_SymbolCols_coeff_mul_congr
-- name    : GlobalTheory.SymbolCols.coeff_mul_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:09.88838+00:00
-- url     : https://prove2.me/theorems/2fd52016-a4c3-4f7f-8cfe-ded53d5a907f
-- title:
--   Symbol Cols: coeff mul congr
-- statement:
--   The Symbol Cols construction uses the coeff mul congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdConstantCoeffDmonOfCols.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdConstantCoeffDmonOfCols.lean#L21-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolCols

theorem GlobalTheory.SymbolCols.coeff_mul_congr {k σ : Type} [CommRing k] (N : ℕ) (f g E : MvPowerSeries σ k)
    (h : ∀ mo : σ →₀ ℕ, mo.degree ≤ N → coeff mo f = coeff mo g)
    (mo : σ →₀ ℕ) (hmo : mo.degree ≤ N) : coeff mo (f * E) = coeff mo (g * E) := by sorry
