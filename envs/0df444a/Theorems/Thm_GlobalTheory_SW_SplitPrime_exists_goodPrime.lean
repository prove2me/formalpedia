-- Prove2me | Theorems.Thm_GlobalTheory_SW_SplitPrime_exists_goodPrime
-- name    : GlobalTheory.SW.SplitPrime.exists_goodPrime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:44:22.278649+00:00
-- url     : https://prove2.me/theorems/3f8feb77-357c-44fd-80f8-3d03add5f4a8
-- title:
--   Split Prime: exists good Prime
-- statement:
--   The Split Prime construction uses the exists good Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmField.lean#L251-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmField.lean#L251-L324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmField
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SplitPrime
open Polynomial
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
open Polynomial

theorem GlobalTheory.SW.SplitPrime.exists_goodPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (m : ℕ), 0 < m → ∃ (q : ℕ) (P : Ideal (𝓞 E)), _root_.GlobalTheory.SW.GoodPrime m q P := by sorry
