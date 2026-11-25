-- Prove2me | Theorems.Thm_GlobalTheory_BetaOfSum_isBeta_block
-- name    : GlobalTheory.BetaOfSum.isBeta_block
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:58.220918+00:00
-- url     : https://prove2.me/theorems/1f0cd142-4e3d-45ab-9bcd-76486174ecc8
-- title:
--   Beta Of Sum: is Beta block
-- statement:
--   The Beta Of Sum construction uses the is Beta block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L134-L143

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n₁ n₂ : ℕ}

theorem GlobalTheory.BetaOfSum.isBeta_block {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {β₁ β₂ : c.F} (b₁ : IsBeta Dw c Λ₁ β₁)
    (b₂ : IsBeta Dw c Λ₂ β₂) : IsBeta Dw c (blockLat Λ₁ Λ₂) (β₁ * β₂) := by sorry
