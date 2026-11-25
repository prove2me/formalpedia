-- Prove2me | Theorems.Thm_GlobalTheory_BetaOfSum_index_block
-- name    : GlobalTheory.BetaOfSum.index_block
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:55.352866+00:00
-- url     : https://prove2.me/theorems/33680af4-16ee-4192-ad30-007445f5f708
-- title:
--   Beta Of Sum: index block
-- statement:
--   The Beta Of Sum construction uses the index block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L107-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L107-L120

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

theorem GlobalTheory.BetaOfSum.index_block (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    ((blockLat Λ₁ Λ₂).Ln.toAddSubgroup.addSubgroupOf (blockLat Λ₁ Λ₂).La.toAddSubgroup).index =
      (Λ₁.Ln.toAddSubgroup.addSubgroupOf Λ₁.La.toAddSubgroup).index *
        (Λ₂.Ln.toAddSubgroup.addSubgroupOf Λ₂.La.toAddSubgroup).index := by sorry
