-- Prove2me | Theorems.Thm_GlobalTheory_abelianScheme_id_pow_finite_etale_surjective
-- name    : GlobalTheory.abelianScheme_id_pow_finite_etale_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:58.786615+00:00
-- url     : https://prove2.me/theorems/14cf65db-841f-45cc-9767-1d39631e5af0
-- title:
--   Global Theory: abelian Scheme id pow finite etale surjective
-- statement:
--   The Global Theory construction uses the abelian Scheme id pow finite etale surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeIdPowFiniteEtaleSurjective.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeIdPowFiniteEtaleSurjective.lean#L14-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeIdPowFiniteEtaleSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.abelianScheme_id_pow_finite_etale_surjective :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (m : ℕ), IsAbelianScheme A → IsUnit (m : Γ(S, ⊤)) → IsMonHom ((𝟙 A) ^ m) ∧ IsFinite ((𝟙 A) ^ m).left ∧ Etale ((𝟙 A) ^ m).left ∧ Surjective ((𝟙 A) ^ m).left := by sorry
