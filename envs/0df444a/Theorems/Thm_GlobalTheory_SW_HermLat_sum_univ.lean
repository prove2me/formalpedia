-- Prove2me | Theorems.Thm_GlobalTheory_SW_HermLat_sum_univ
-- name    : GlobalTheory.SW.HermLat.sum_univ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:18.026224+00:00
-- url     : https://prove2.me/theorems/aabea1d7-2180-489d-adbd-b1730396716f
-- title:
--   Herm Lat: sum univ
-- statement:
--   The Herm Lat construction uses the sum univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsIntegralBasisHermitianMatricesDual.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsIntegralBasisHermitianMatricesDual.lean#L20-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.HermLat.sum_univ {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (g : (E →+* ℂ) → ℂ) :
    ∑ σ, g σ = ∑ τ : Ψ, (g τ + g (ComplexEmbedding.conjugate τ.1)) := by sorry
