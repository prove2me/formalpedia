-- Prove2me | Theorems.Thm_GlobalTheory_CoeffRings_coeff_isDedFrac
-- name    : GlobalTheory.CoeffRings.coeff_isDedFrac
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:16:20.141206+00:00
-- url     : https://prove2.me/theorems/5a33a12d-5d7e-4543-bda3-8ab5122fd473
-- title:
--   Coeff Rings: coeff is Ded Frac
-- statement:
--   The Coeff Rings construction uses the coeff is Ded Frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoefficientFieldIntegersDedekindFractionField.lean#L188-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoefficientFieldIntegersDedekindFractionField.lean#L188-L264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoefficientFieldIntegersDedekindFractionField
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
open GlobalTheory GlobalTheory.CoeffRings
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.CoeffRings.coeff_isDedFrac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Models.IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) ∧ (∀ A : ℕ, A ∣ l.A → ∃ b : _root_.GlobalTheory.Models.RZ H 1 A →+* 𝓞 c.F, _root_.GlobalTheory.Models.IsInc (_root_.GlobalTheory.Models.RZ H 1 A).subtype (c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)) b) ∧ ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → _root_.GlobalTheory.Models.IsDedFrac (c.V W).subtype ∧ (∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)) ∧ ∀ S A : ℕ, S.Coprime p → 0 < A → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A ∈ c.F → ∃ b : _root_.GlobalTheory.Models.RZ H S A →+* c.V W, _root_.GlobalTheory.Models.IsInc (_root_.GlobalTheory.Models.RZ H S A).subtype (c.F.val.toRingHom.comp (c.V W).subtype) b := by sorry
