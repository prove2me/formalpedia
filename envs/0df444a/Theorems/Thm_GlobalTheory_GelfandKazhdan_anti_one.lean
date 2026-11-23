-- Prove2me | Theorems.Thm_GlobalTheory_GelfandKazhdan_anti_one
-- name    : GlobalTheory.GelfandKazhdan.anti_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:07.584569+00:00
-- url     : https://prove2.me/theorems/9cd93f3a-0809-4f50-9628-2a9af4f21301
-- title:
--   Gelfand Kazhdan: anti one
-- statement:
--   The Gelfand Kazhdan construction uses the anti one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransposeInvariantOfConjInvariantDistributionGL.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransposeInvariantOfConjInvariantDistributionGL.lean#L24-L27

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

theorem GlobalTheory.GelfandKazhdan.anti_one {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) : t 1 = 1 := by sorry
