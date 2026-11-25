-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_map_torsionIdeal
-- name    : GlobalTheory.PDiv.map_torsionIdeal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:06.847232+00:00
-- url     : https://prove2.me/theorems/a14949aa-8989-484d-bab9-1b423da132d1
-- title:
--   PDiv: map torsion Ideal
-- statement:
--   The PDiv construction uses the map torsion Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L163-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_IsBicharacter_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

theorem GlobalTheory.PDiv.map_torsionIdeal [IsCocomm R C] [IsCocomm R A] {f : C →ₐc[R] A}
    (hf : Function.Surjective f) (n : ℕ) :
    Ideal.map (f : C →ₐ[R] A) (torsionIdeal R C n) = torsionIdeal R A n := by sorry
