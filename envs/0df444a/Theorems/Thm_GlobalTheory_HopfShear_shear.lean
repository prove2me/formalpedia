-- Prove2me | Theorems.Thm_GlobalTheory_HopfShear_shear
-- name    : GlobalTheory.HopfShear.shear
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:52.176773+00:00
-- url     : https://prove2.me/theorems/c7e50e51-f3da-4ca5-b312-1156be1f4ab6
-- title:
--   Hopf Shear: shear
-- statement:
--   The Hopf Shear construction uses the shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L49-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L49-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct WithConv
open GlobalTheory GlobalTheory.HopfShear
variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]
attribute [local instance] pointsGroup

theorem GlobalTheory.HopfShear.shear (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
    [HopfAlgebra R B] (f : B →ₐc[R] A) :
    Nonempty ((TensorProduct (AlgHom.range (f : B →ₐ[R] A)) A A) ≃ₗ[A]
      TensorProduct R A (A ⧸ Ideal.map (f : B →ₐ[R] A)
        (RingHom.ker (Bialgebra.counitAlgHom R B)))) := by sorry
