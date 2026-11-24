-- Prove2me | Theorems.Thm_GlobalTheory_isNormalScheme_pullback_spMap_of_algebra
-- name    : GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:24.308798+00:00
-- url     : https://prove2.me/theorems/8cdc5cd7-d1fc-44f3-8e75-6076b4a749a2
-- title:
--   Global Theory: is Normal Scheme pullback sp Map of algebra
-- statement:
--   The Global Theory construction uses the is Normal Scheme pullback sp Map of algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsNormalSchemePullbackSpMapOfAlgebra.lean#L6-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsNormalSchemePullbackSpMapOfAlgebra.lean#L6-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsNormalSchemePullbackSpMapOfAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
    (halg : ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A]
      [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧
        IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
        IsIntegrallyClosed (Localization.AtPrime Q))
    (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0})
    (g : Y ⟶ Sp F) (hY : GlobalTheory.IsNormalScheme Y) : GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by sorry
