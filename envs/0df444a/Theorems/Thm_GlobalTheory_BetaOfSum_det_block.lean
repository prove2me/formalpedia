-- Prove2me | Theorems.Thm_GlobalTheory_BetaOfSum_det_block
-- name    : GlobalTheory.BetaOfSum.det_block
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:34.374906+00:00
-- url     : https://prove2.me/theorems/206ee8f6-4e5d-4b99-8a46-70f9dc240322
-- title:
--   Beta Of Sum: det block
-- statement:
--   The Beta Of Sum construction uses the det block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L24-L32

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
omit [NumberField E]

theorem GlobalTheory.BetaOfSum.det_block (u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h : ∀ i j, u (Fin.castAdd n₂ i) (Fin.natAdd n₁ j) = 0) :
    u.det = (Matrix.of fun i j => u (Fin.castAdd n₂ i) (Fin.castAdd n₂ j)).det *
      (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.natAdd n₁ j)).det := by sorry
