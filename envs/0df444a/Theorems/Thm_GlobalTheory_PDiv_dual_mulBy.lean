-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_dual_mulBy
-- name    : GlobalTheory.PDiv.dual_mulBy
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:53.862657+00:00
-- url     : https://prove2.me/theorems/bb9dfdc2-109f-4130-a751-606f9a073df0
-- title:
--   PDiv: dual mul By
-- statement:
--   The PDiv construction uses the dual mul By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L291-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L291-L292

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
variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R C] [Module.Projective R C]
  [IsCocomm R A] [IsCocomm R C]

theorem GlobalTheory.PDiv.dual_mulBy (n : ℕ) : CartierDual.map (mulBy R A n) = mulBy R (CartierDual R A) n := by sorry
