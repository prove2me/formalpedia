-- Prove2me | Theorems.Thm_GlobalTheory_RowKernel_card_add_le
-- name    : GlobalTheory.RowKernel.card_add_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-27T06:16:07.234044+00:00
-- url     : https://prove2.me/theorems/6c0cdd47-b7cb-4767-a25e-1a3ec9202ecb
-- title:
--   Row Kernel: card add le
-- statement:
--   The Row Kernel construction uses the card add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugedFormalGroupKernelSmallOfSecond.lean#L50-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugedFormalGroupKernelSmallOfSecond.lean#L50-L130

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupKernelSmallOfSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowKernel
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.RowKernel.card_add_le {σ : Type} [Fintype σ] (p : σ → Prop) [DecidablePred p] {N M : ℕ}
    (A : Fin N → σ → C) (B : Fin M → σ → C) (hA : IndepMod V A) (hAp : ∀ ν s, ¬ p s → A ν s = 0)
    (hB : IsSat V B) (hBp : ∀ μ s, ¬ p s → B μ s = 0) (hAB : ∀ ν μ, V.MM (∑ s, A ν s * B μ s)) :
    N + M ≤ (Finset.univ.filter p).card := by sorry
