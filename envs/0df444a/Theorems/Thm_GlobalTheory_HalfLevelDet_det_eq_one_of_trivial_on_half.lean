-- Prove2me | Theorems.Thm_GlobalTheory_HalfLevelDet_det_eq_one_of_trivial_on_half
-- name    : GlobalTheory.HalfLevelDet.det_eq_one_of_trivial_on_half
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:29.458516+00:00
-- url     : https://prove2.me/theorems/bfb85d3e-0f2c-424d-bcc0-4a0ca8fb5fa3
-- title:
--   Half Level Det: det eq one of trivial on half
-- statement:
--   The Half Level Det construction uses the det eq one of trivial on half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetEqOneOfTrivialOnHalf.lean#L56-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetEqOneOfTrivialOnHalf.lean#L56-L86

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryMatrixOfLatticeIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetEqOneOfTrivialOnHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.HalfLevelDet

theorem GlobalTheory.HalfLevelDet.det_eq_one_of_trivial_on_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : Dw.La ≃ₗ[𝓞 E] Dw.La), (∀ a b, Dw.EF (γ a) (γ b) = Dw.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ e, γ a = a + l.M • e) → LinearMap.det (LinearMap.baseChange E (γ : Dw.La →ₗ[𝓞 E] Dw.La)) = 1 := by sorry
