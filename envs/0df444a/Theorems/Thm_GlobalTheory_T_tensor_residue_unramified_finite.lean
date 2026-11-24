-- Prove2me | Theorems.Thm_GlobalTheory_T_tensor_residue_unramified_finite
-- name    : GlobalTheory.T.tensor_residue_unramified_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:00:00.567939+00:00
-- url     : https://prove2.me/theorems/fc851406-0417-473e-a9be-3eccb64ab3f0
-- title:
--   T: tensor residue unramified finite
-- statement:
--   The T construction uses the tensor residue unramified finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorResidueUnramifiedFiniteStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorResidueUnramifiedFiniteStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorResidueUnramifiedFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorResidueUnramifiedFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tensor_residue_unramified_finite : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B] [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite → ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified → Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧ Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by sorry
