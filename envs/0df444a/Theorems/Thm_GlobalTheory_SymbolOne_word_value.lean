-- Prove2me | Theorems.Thm_GlobalTheory_SymbolOne_word_value
-- name    : GlobalTheory.SymbolOne.word_value
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:46.45427+00:00
-- url     : https://prove2.me/theorems/ad11f140-ca02-4330-b691-4ac55cbb0e70
-- title:
--   Symbol One: word value
-- statement:
--   The Symbol One construction uses the word value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L117-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L117-L184

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

theorem GlobalTheory.SymbolOne.word_value (π : A →ₐ[k] k) (D : ι → Derivation k A A) (lam : ι → A)
    (hlam : ∀ l, π (lam l) = 0) (α : ι → k) (w : List ι) (a : ι → ℕ) (E : A)
    (hD : ∀ l l', a l ≠ 0 → l' ∈ w → π (D l' (lam l)) = if l = l' then α l else 0)
    (hw : w.length ≤ ∑ l, a l) :
    π (w.foldl (fun g l => D l g) ((∏ l, lam l ^ a l) * E)) =
      if (∀ l, w.count l = a l) then (∏ l, ((a l).factorial : k) * α l ^ a l) * π E else 0 := by sorry
