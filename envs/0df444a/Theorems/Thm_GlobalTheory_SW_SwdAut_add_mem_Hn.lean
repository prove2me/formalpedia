-- Prove2me | Theorems.Thm_GlobalTheory_SW_SwdAut_add_mem_Hn
-- name    : GlobalTheory.SW.SwdAut.add_mem_Hn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:09.755381+00:00
-- url     : https://prove2.me/theorems/8cc7759e-3d1a-45dd-b4d1-b30160a38693
-- title:
--   Swd Aut: add mem Hn
-- statement:
--   The Swd Aut construction uses the add mem Hn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDifferenceAutomorphyLinearity.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDifferenceAutomorphyLinearity.lean#L42-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearity
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdAut
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

theorem GlobalTheory.SW.SwdAut.add_mem_Hn (Ψ : Finset (E →+* ℂ)) {β : Matrix (Fin N) (Fin N) E} (hβ : ccT β = β)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : (fun τ => Z τ + β.map τ.1 : CM Ψ N N) ∈ Hn Ψ N := by sorry
