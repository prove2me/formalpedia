-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_good_split_prime_cmField
-- name    : GlobalTheory.T.exists_good_split_prime_cmField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:44.870195+00:00
-- url     : https://prove2.me/theorems/d192a081-ae80-404f-ae84-e5a8214d0589
-- title:
--   T: exists good split prime cm Field
-- statement:
--   The T construction uses the exists good split prime cm Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmFieldStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmFieldStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmFieldStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_good_split_prime_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ), 0 < m → ∃ (q : ℕ) (P : Ideal (𝓞 E)), GoodPrime m q P := by sorry
