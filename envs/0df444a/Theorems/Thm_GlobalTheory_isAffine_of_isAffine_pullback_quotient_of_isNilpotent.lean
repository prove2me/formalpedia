-- Prove2me | Theorems.Thm_GlobalTheory_isAffine_of_isAffine_pullback_quotient_of_isNilpotent
-- name    : GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:50.952578+00:00
-- url     : https://prove2.me/theorems/24a62691-44f0-49ba-8afd-aa562ab93cc6
-- title:
--   Global Theory: is Affine of is Affine pullback quotient of is Nilpotent
-- statement:
--   The Global Theory construction uses the is Affine of is Affine pullback quotient of is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L372-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L372-L377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory

theorem GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent (A : Type) [CommRing A]
    (J : Ideal A) (hJ : IsNilpotent J) (Y : Over (Spec (CommRingCat.of A)))
    (h : IsAffine (pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) :
    IsAffine Y.left := by sorry
