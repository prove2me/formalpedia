-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_exists_separating_rational
-- name    : GroundTheory.Arith.Toric.exists_separating_rational
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:56:20.907245+00:00
-- url     : https://prove2.me/theorems/9b1513ac-faad-48b5-a477-b9bc754528b8
-- title:
--   Toric: exists separating rational
-- statement:
--   The Toric construction uses the exists separating rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L44-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L44-L88

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.exists_separating_rational {σ σ' : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hσ' : IsRationalPolyhedral (toRealSpan N) σ')
    (h : (σ ⊓ σ').IsFaceOf σ) (h' : (σ ⊓ σ').IsFaceOf σ') :
    ∃ u : Dual ℤ N, u ∈ dualMonoid σ ∧ -u ∈ dualMonoid σ' ∧
      exposedFace σ (toRealDual N u) = σ ⊓ σ' ∧ exposedFace σ' (toRealDual N u) = σ ⊓ σ' := by sorry
