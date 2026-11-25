-- Prove2me | Theorems.Thm_GlobalTheory_T_coefficientField_integers_dedekind_fractionField
-- name    : GlobalTheory.T.coefficientField_integers_dedekind_fractionField
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:02.869789+00:00
-- url     : https://prove2.me/theorems/55c81ff5-da02-55eb-99bb-e3ad8309e29b
-- title:
--   T: coefficient Field integers dedekind fraction Field
-- statement:
--   The T construction uses the coefficient Field integers dedekind fraction Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoefficientFieldIntegersDedekindFractionFieldStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoefficientFieldIntegersDedekindFractionFieldStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoefficientFieldIntegersDedekindFractionField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoefficientFieldIntegersDedekindFractionFieldStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem GlobalTheory.T.coefficientField_integers_dedekind_fractionField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l), IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) ∧ (∀ A : ℕ, A ∣ l.A → ∃ b : RZ H 1 A →+* 𝓞 c.F, IsInc (RZ H 1 A).subtype (c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)) b) ∧ ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → IsDedFrac (c.V W).subtype ∧ (∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)) ∧ ∀ S A : ℕ, S.Coprime p → 0 < A → zeta A ∈ c.F → ∃ b : RZ H S A →+* c.V W, IsInc (RZ H S A).subtype (c.F.val.toRingHom.comp (c.V W).subtype) b := by sorry
