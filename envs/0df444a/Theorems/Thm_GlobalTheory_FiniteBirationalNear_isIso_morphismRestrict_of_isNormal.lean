-- Prove2me | Theorems.Thm_GlobalTheory_FiniteBirationalNear_isIso_morphismRestrict_of_isNormal
-- name    : GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:28:31.17336+00:00
-- url     : https://prove2.me/theorems/37318c75-92ed-4900-b4b2-84ad10353405
-- title:
--   Finite Birational Near: is Iso morphism Restrict of is Normal
-- statement:
--   The Finite Birational Near construction uses the is Iso morphism Restrict of is Normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoMorphismRestrictFiniteOfIsNormalDense.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoMorphismRestrictFiniteOfIsNormalDense.lean#L9-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoMorphismRestrictFiniteOfIsNormalDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FiniteBirationalNear

theorem GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by sorry
