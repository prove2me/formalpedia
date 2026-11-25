-- Prove2me | Theorems.Thm_GlobalTheory_T_isNormalScheme_pullback_spMap_of_isNormalScheme
-- name    : GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:48.930962+00:00
-- url     : https://prove2.me/theorems/25a3c800-71da-5bf1-9f3c-318faf6ff4ef
-- title:
--   T: is Normal Scheme pullback sp Map of is Normal Scheme
-- statement:
--   The T construction uses the is Normal Scheme pullback sp Map of is Normal Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsNormalSchemePullbackSpMapOfAlgebraStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsNormalSchemePullbackSpMapOfAlgebraStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsNormalSchemePullbackSpMapOfAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsNormalSchemePullbackSpMapOfAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme : (∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by sorry
