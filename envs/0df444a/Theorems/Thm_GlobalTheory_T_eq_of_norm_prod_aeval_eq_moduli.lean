-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_of_norm_prod_aeval_eq_moduli
-- name    : GlobalTheory.T.eq_of_norm_prod_aeval_eq_moduli
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:33:06.653681+00:00
-- url     : https://prove2.me/theorems/8e40ee6e-49bb-4576-9f90-35cd448c26a2
-- title:
--   T: eq of norm prod aeval eq moduli
-- statement:
--   The T construction uses the eq of norm prod aeval eq moduli property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEqStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEqStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
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

theorem GlobalTheory.T.eq_of_norm_prod_aeval_eq_moduli : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ_[l] Ω] [Algebra.IsAlgebraic ℚ_[l] Ω] (a b : Multiset Ω) (P Q : Polynomial ℚ_[l]), P.map (algebraMap ℚ_[l] Ω) = (a.map fun x => Polynomial.X - Polynomial.C x).prod → Q.map (algebraMap ℚ_[l] Ω) = (b.map fun x => Polynomial.X - Polynomial.C x).prod → (∀ (F : Polynomial ℤ) (u v : ℚ_[l]), algebraMap ℚ_[l] Ω u = (a.map fun x => Polynomial.aeval x F).prod → algebraMap ℚ_[l] Ω v = (b.map fun x => Polynomial.aeval x F).prod → ‖u‖ = ‖v‖) → P = Q := by sorry
