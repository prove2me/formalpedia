-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_complex_stable_iff_exists_baseChange
-- name    : GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:16.024849+00:00
-- url     : https://prove2.me/theorems/64ef22cb-36bc-582a-bca2-1a9e0bb9a479
-- title:
--   Galois Descent: complex stable iff exists base Change
-- statement:
--   The Galois Descent construction uses the complex stable iff exists base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankFixedSubmoduleComplexification.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankFixedSubmoduleComplexification.lean#L31-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankFixedSubmoduleComplexification
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry
universe u
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Algebra K ℂ]

theorem GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange {V : Type*} [AddCommGroup V]
    [Module K V] (W : Submodule ℂ (ℂ ⊗[K] V)) :
    (∀ σ : ℂ ≃ₐ[K] ℂ, ∀ w ∈ W, σ.toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange ℂ = W := by sorry
