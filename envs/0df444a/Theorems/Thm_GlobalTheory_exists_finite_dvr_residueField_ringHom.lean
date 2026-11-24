-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_dvr_residueField_ringHom
-- name    : GlobalTheory.exists_finite_dvr_residueField_ringHom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:38.230808+00:00
-- url     : https://prove2.me/theorems/68aea852-4752-4cd0-a8ed-73fedfeac29b
-- title:
--   Global Theory: exists finite dvr residue Field ring Hom
-- statement:
--   The Global Theory construction uses the exists finite dvr residue Field ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFiniteDvrExtensionEmbeddingResidueField.lean#L102-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFiniteDvrExtensionEmbeddingResidueField.lean#L102-L129

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFiniteDvrExtensionEmbeddingResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing

theorem GlobalTheory.exists_finite_dvr_residueField_ringHom :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] (k' : Type) [Field k'] [Algebra (ResidueField W) k'] [FiniteDimensional (ResidueField W) k'], ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W') (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'), Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ ∃ e : k' →+* ResidueField W', ∀ v : W, e (algebraMap (ResidueField W) k' (residue W v)) = residue W' (algebraMap W W' v) := by sorry
