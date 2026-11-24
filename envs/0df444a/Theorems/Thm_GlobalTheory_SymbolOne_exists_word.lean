-- Prove2me | Theorems.Thm_GlobalTheory_SymbolOne_exists_word
-- name    : GlobalTheory.SymbolOne.exists_word
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:48.429031+00:00
-- url     : https://prove2.me/theorems/ae896fc3-d191-4b61-81fb-7e50249d78c8
-- title:
--   Symbol One: exists word
-- statement:
--   The Symbol One construction uses the exists word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L188-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L188-L205

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

theorem GlobalTheory.SymbolOne.exists_word {ι A : Type} [DecidableEq ι] (D : ι → A → A) (m : ι → ℕ) (L : List ι) :
    ∃ w : List ι, (∀ l, w.count l = L.count l * m l) ∧
      ∀ f, L.foldr (fun l g => (D l)^[m l] g) f = w.foldl (fun g l => D l g) f := by sorry
