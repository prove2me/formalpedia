-- Prove2me | Theorems.Thm_GlobalTheory_BetaOfSum_block_Ln
-- name    : GlobalTheory.BetaOfSum.block_Ln
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:58.597483+00:00
-- url     : https://prove2.me/theorems/46b7a814-fb9c-48ae-b4de-6e88dc012431
-- title:
--   Beta Of Sum: block Ln
-- statement:
--   The Beta Of Sum construction uses the block Ln property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L100-L105

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

theorem GlobalTheory.BetaOfSum.block_Ln (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    (blockLat Λ₁ Λ₂).Ln = (blockLat ⟨Λ₁.Ln⟩ ⟨Λ₂.Ln⟩).La := by sorry
