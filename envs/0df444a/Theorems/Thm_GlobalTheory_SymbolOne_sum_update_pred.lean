-- Prove2me | Theorems.Thm_GlobalTheory_SymbolOne_sum_update_pred
-- name    : GlobalTheory.SymbolOne.sum_update_pred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:52.854393+00:00
-- url     : https://prove2.me/theorems/d292f932-66db-45ac-82d7-ea66295564f9
-- title:
--   Symbol One: sum update pred
-- statement:
--   The Symbol One construction uses the sum update pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L56-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolOne
variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SymbolOne.sum_update_pred (a : ι → ℕ) (j : ι) (h : a j ≠ 0) :
    ∑ l, Function.update a j (a j - 1) l + 1 = ∑ l, a l := by sorry
