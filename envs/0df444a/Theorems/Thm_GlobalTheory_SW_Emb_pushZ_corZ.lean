-- Prove2me | Theorems.Thm_GlobalTheory_SW_Emb_pushZ_corZ
-- name    : GlobalTheory.SW.Emb.pushZ_corZ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:39:12.212668+00:00
-- url     : https://prove2.me/theorems/8eefa41b-06b6-4b29-8bc9-c0096d40c1c5
-- title:
--   Emb: push Z cor Z
-- statement:
--   The Emb construction uses the push Z cor Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L182-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L182-L187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.Emb.pushZ_corZ (Z : CM Ψ N N) (t : ℝ) :
    pushZ Ψ (corZ I Z) (Pi.single 0 1) t = corZ (I + I * t) Z := by sorry
