-- Prove2me | Theorems.Thm_GlobalTheory_SW_HermLat_half_trace
-- name    : GlobalTheory.SW.HermLat.half_trace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:36.299802+00:00
-- url     : https://prove2.me/theorems/e5e8be45-1d32-40ff-9847-d80b0748c13f
-- title:
--   Herm Lat: half trace
-- statement:
--   The Herm Lat construction uses the half trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsIntegralBasisHermitianMatricesDual.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsIntegralBasisHermitianMatricesDual.lean#L36-L48

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

theorem GlobalTheory.SW.HermLat.half_trace {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {x : E} (hx : cc x = x) :
    (((1 / 2 : ℚ) * Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : Ψ, τ.1 x := by sorry
