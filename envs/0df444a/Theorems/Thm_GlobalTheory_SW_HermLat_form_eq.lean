-- Prove2me | Theorems.Thm_GlobalTheory_SW_HermLat_form_eq
-- name    : GlobalTheory.SW.HermLat.form_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:30.455549+00:00
-- url     : https://prove2.me/theorems/ad70229a-d63a-4bcc-9925-6e656dc02408
-- title:
--   Herm Lat: form eq
-- statement:
--   The Herm Lat construction uses the form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsIntegralBasisHermitianMatricesDual.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsIntegralBasisHermitianMatricesDual.lean#L107-L109

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

theorem GlobalTheory.SW.HermLat.form_eq {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {N : ℕ} (X Y : HermSub E N) :
    ((form E N X Y : ℚ) : ℂ) = ∑ τ : Ψ, τ.1 (X.1 * Y.1).trace := by sorry
