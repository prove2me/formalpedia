-- Prove2me | Theorems.Thm_GlobalTheory_SW_SplitPrime_absNorm_prime
-- name    : GlobalTheory.SW.SplitPrime.absNorm_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:27.133815+00:00
-- url     : https://prove2.me/theorems/d148e7d3-efff-44a2-ae86-5d16a8680bd0
-- title:
--   Split Prime: abs Norm prime
-- statement:
--   The Split Prime construction uses the abs Norm prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmField.lean#L227-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmField.lean#L227-L245

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

theorem GlobalTheory.SW.SplitPrime.absNorm_prime {E : Type} [Field E] [NumberField E]
    (P : Ideal (𝓞 E)) (hP : P.IsMaximal)
    (hs : Function.Surjective (Int.castRingHom (𝓞 E ⧸ P))) : (Ideal.absNorm P).Prime := by sorry
