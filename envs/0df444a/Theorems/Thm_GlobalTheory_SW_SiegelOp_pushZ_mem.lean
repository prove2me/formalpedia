-- Prove2me | Theorems.Thm_GlobalTheory_SW_SiegelOp_pushZ_mem
-- name    : GlobalTheory.SW.SiegelOp.pushZ_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:09.095958+00:00
-- url     : https://prove2.me/theorems/f7e95c6c-aec4-4a3b-b869-1175101f54da
-- title:
--   Siegel Op: push Z mem
-- statement:
--   The Siegel Op construction uses the push Z mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHSiegelOperator.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHSiegelOperator.lean#L17-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperator
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelOp
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
omit [NumberField E]

theorem GlobalTheory.SW.SiegelOp.pushZ_mem {Z : CM Ψ N N} (h : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by sorry
