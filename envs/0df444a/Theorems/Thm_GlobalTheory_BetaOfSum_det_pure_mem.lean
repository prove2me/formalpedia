-- Prove2me | Theorems.Thm_GlobalTheory_BetaOfSum_det_pure_mem
-- name    : GlobalTheory.BetaOfSum.det_pure_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:29.50211+00:00
-- url     : https://prove2.me/theorems/3c478e0f-f7d8-42a5-a176-dd469df5629b
-- title:
--   Beta Of Sum: det pure mem
-- statement:
--   The Beta Of Sum construction uses the det pure mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBetaUnitBlock.lean#L36-L54

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

theorem GlobalTheory.BetaOfSum.det_pure_mem (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (w : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h₁ : ∀ i, (fun j => w i (Fin.castAdd n₂ j)) ∈ M₁) (h₂ : ∀ i, (fun j => w i (Fin.natAdd n₁ j)) ∈ M₂)
    (h : ∀ i, (∀ j, w i (Fin.castAdd n₂ j) = 0) ∨ ∀ j, w i (Fin.natAdd n₁ j) = 0) :
    w.det ∈ detSpan M₁ * detSpan M₂ := by sorry
