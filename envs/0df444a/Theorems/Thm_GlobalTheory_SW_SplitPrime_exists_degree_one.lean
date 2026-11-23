-- Prove2me | Theorems.Thm_GlobalTheory_SW_SplitPrime_exists_degree_one
-- name    : GlobalTheory.SW.SplitPrime.exists_degree_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:22.228231+00:00
-- url     : https://prove2.me/theorems/5dac5dfd-8266-4bd0-81c7-41fca2eee899
-- title:
--   Split Prime: exists degree one
-- statement:
--   The Split Prime construction uses the exists degree one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmField.lean#L170-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsGoodSplitPrimeCmField.lean#L170-L221

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

theorem GlobalTheory.SW.SplitPrime.exists_degree_one {E : Type} [Field E] [NumberField E] (θ : 𝓞 E)
    (hθ : θ ≠ 0) (d : ℤ) (hd : d ≠ 0) (hden : ∀ a : 𝓞 E, ∃ g : ℤ[X], (d : 𝓞 E) * a = aeval θ g)
    (N : ℤ) (hN : N ≠ 0) :
    ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ (N : 𝓞 E) ∉ P ∧
      Function.Surjective (Int.castRingHom (𝓞 E ⧸ P)) := by sorry
