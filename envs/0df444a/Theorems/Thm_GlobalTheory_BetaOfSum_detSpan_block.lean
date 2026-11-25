-- Prove2me | Theorems.Thm_GlobalTheory_BetaOfSum_detSpan_block
-- name    : GlobalTheory.BetaOfSum.detSpan_block
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:46.269285+00:00
-- url     : https://prove2.me/theorems/d5cbba15-cf99-454f-b1f4-61d0449b61fc
-- title:
--   Beta Of Sum: det Span block
-- statement:
--   The Beta Of Sum construction uses the det Span block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L56-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L56-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock
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
open GlobalTheory GlobalTheory.BetaOfSum
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BetaEx GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility GlobalTheory.ShortLawsCompare
variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

theorem GlobalTheory.BetaOfSum.detSpan_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) :
    detSpan (blockLat ⟨M₁⟩ ⟨M₂⟩).La = detSpan M₁ * detSpan M₂ := by sorry
