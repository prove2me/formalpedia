-- Prove2me | Theorems.Thm_GlobalTheory_SymbolOne_word_add
-- name    : GlobalTheory.SymbolOne.word_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:29.270816+00:00
-- url     : https://prove2.me/theorems/d1c1a9ba-2f44-478b-a027-3798400dc0a4
-- title:
--   Symbol One: word add
-- statement:
--   The Symbol One construction uses the word add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L37-L41

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

theorem GlobalTheory.SymbolOne.word_add (D : ι → Derivation k A A) (w : List ι) (x y : A) :
    w.foldl (fun g l => D l g) (x + y) = w.foldl (fun g l => D l g) x + w.foldl (fun g l => D l g) y := by sorry
