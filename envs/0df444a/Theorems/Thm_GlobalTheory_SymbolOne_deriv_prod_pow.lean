-- Prove2me | Theorems.Thm_GlobalTheory_SymbolOne_deriv_prod_pow
-- name    : GlobalTheory.SymbolOne.deriv_prod_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:23.34915+00:00
-- url     : https://prove2.me/theorems/e7e756e0-9a63-45b9-9806-588167692a7f
-- title:
--   Symbol One: deriv prod pow
-- statement:
--   The Symbol One construction uses the deriv prod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L76-L87

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

theorem GlobalTheory.SymbolOne.deriv_prod_pow (D : Derivation k A A) (lam : ι → A) (a : ι → ℕ) :
    D (∏ l, lam l ^ a l) =
      ∑ j, (a j : A) * (∏ l, lam l ^ Function.update a j (a j - 1) l) * D (lam j) := by sorry
