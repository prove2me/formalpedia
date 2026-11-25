-- Prove2me | Theorems.Thm_GlobalTheory_T_isIso_morphismRestrict_finite_of_isNormal_dense
-- name    : GlobalTheory.T.isIso_morphismRestrict_finite_of_isNormal_dense
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:28.991821+00:00
-- url     : https://prove2.me/theorems/ad6e558b-9809-48cb-912b-78e4783f90a5
-- title:
--   T: is Iso morphism Restrict finite of is Normal dense
-- statement:
--   The T construction uses the is Iso morphism Restrict finite of is Normal dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoMorphismRestrictFiniteOfIsNormalDenseStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoMorphismRestrictFiniteOfIsNormalDenseStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoMorphismRestrictFiniteOfIsNormalDense
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoMorphismRestrictFiniteOfIsNormalDenseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIso_morphismRestrict_finite_of_isNormal_dense : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by sorry
