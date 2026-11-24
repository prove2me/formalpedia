-- Prove2me | Theorems.Thm_GlobalTheory_HalfLevelDet_det_baseChange_eq
-- name    : GlobalTheory.HalfLevelDet.det_baseChange_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:36:56.461167+00:00
-- url     : https://prove2.me/theorems/52e53ae8-e2b2-4a7c-925b-8d53eaad79dc
-- title:
--   Half Level Det: det base Change eq
-- statement:
--   The Half Level Det construction uses the det base Change eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetEqOneOfTrivialOnHalf.lean#L24-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetEqOneOfTrivialOnHalf.lean#L24-L54

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

theorem GlobalTheory.HalfLevelDet.det_baseChange_eq {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] (hr : Module.finrank (𝓞 E) L = r)
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (f : L →ₗ[𝓞 E] L) (g : Matrix (Fin r) (Fin r) E) (hg : ∀ a, φ (f a) = g *ᵥ φ a) :
    LinearMap.det (LinearMap.baseChange E f) = g.det := by sorry
