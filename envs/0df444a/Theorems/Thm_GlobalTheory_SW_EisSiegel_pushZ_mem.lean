-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisSiegel_pushZ_mem
-- name    : GlobalTheory.SW.EisSiegel.pushZ_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:58.964644+00:00
-- url     : https://prove2.me/theorems/d1bd023d-4a77-4739-bce9-48f4ad152794
-- title:
--   Eis Siegel: push Z mem
-- statement:
--   The Eis Siegel construction uses the push Z mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelOperatorHermitianEisensteinSeries.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelOperatorHermitianEisensteinSeries.lean#L54-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelOperatorHermitianEisensteinSeries
import Theorems.Thm_GlobalTheory_SW_SiegelOp_pushZ_mem

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisSiegel
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.EisSiegel.pushZ_mem {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by sorry
