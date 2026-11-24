-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_exists_isAffineOpen_preimage_eq_of_isNilpotent
-- name    : GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:42.439448+00:00
-- url     : https://prove2.me/theorems/94d75865-f682-4323-95d7-8f074317ed2e
-- title:
--   Affine Thickening: exists is Affine Open preimage eq of is Nilpotent
-- statement:
--   The Affine Thickening construction uses the exists is Affine Open preimage eq of is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsAffineOpenPreimageEqOfIsNilpotent.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsAffineOpenPreimageEqOfIsNilpotent.lean#L8-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenPreimageEqOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.AffineThickening

theorem GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A') (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g))
    (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A'))
    (β : X' ⟶ X) (h : IsPullback β f' f (Spec.map (CommRingCat.ofHom g)))
    (D' : X'.Opens) (hD' : IsAffineOpen D') :
    ∃ D : X.Opens, IsAffineOpen D ∧ β ⁻¹ᵁ D = D' := by sorry
