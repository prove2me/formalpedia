-- Prove2me | Theorems.Thm_GlobalTheory_GelfandKazhdan_anti_inv
-- name    : GlobalTheory.GelfandKazhdan.anti_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:23.001209+00:00
-- url     : https://prove2.me/theorems/aedfbdb2-0784-4ed9-a332-edab43f0f351
-- title:
--   Gelfand Kazhdan: anti inv
-- statement:
--   The Gelfand Kazhdan construction uses the anti inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransposeInvariantOfConjInvariantDistributionGL.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransposeInvariantOfConjInvariantDistributionGL.lean#L30-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaireStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhausStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
noncomputable section
open GlobalTheory GlobalTheory.GelfandKazhdan
variable {G : Type} [Group G] [TopologicalSpace G]
omit [TopologicalSpace G]

theorem GlobalTheory.GelfandKazhdan.anti_inv {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) (x : G) : t x⁻¹ = (t x)⁻¹ := by sorry
