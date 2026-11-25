-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_isLocalization_away_semigroupAlgebra
-- name    : GroundTheory.Arith.Toric.isLocalization_away_semigroupAlgebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:55:53.038211+00:00
-- url     : https://prove2.me/theorems/7c510f4c-5403-56a6-a57e-2cd63bfc3ecc
-- title:
--   Toric: is Localization away semigroup Algebra
-- statement:
--   The Toric construction uses the is Localization away semigroup Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L137-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L137-L179

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry
universe u
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

theorem GroundTheory.Arith.Toric.isLocalization_away_semigroupAlgebra {S T : AddSubmonoid G} (h : S ≤ T) {u : G}
    (hu : u ∈ S) (hu' : -u ∈ T) (hT : ∀ m ∈ T, ∃ j : ℕ, m + j • u ∈ S) :
    letI := semigroupAlgebraAlgebra (k := k) h
    IsLocalization.Away (⟨single u 1, single_mem_semigroupAlgebra hu 1⟩ : semigroupAlgebra k S)
      (semigroupAlgebra k T) := by sorry
