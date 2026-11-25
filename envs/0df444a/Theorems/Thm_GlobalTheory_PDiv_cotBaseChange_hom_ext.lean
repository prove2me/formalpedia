-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_cotBaseChange_hom_ext
-- name    : GlobalTheory.PDiv.cotBaseChange_hom_ext
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:01:20.444947+00:00
-- url     : https://prove2.me/theorems/07604e72-3e38-5bf5-a7a3-f114c858b62f
-- title:
--   PDiv: cot Base Change hom ext
-- statement:
--   The PDiv construction uses the cot Base Change hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijective.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijective.lean#L44-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv
variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']

theorem GlobalTheory.PDiv.cotBaseChange_hom_ext {N : Type} [AddCommGroup N] [Module R' N]
    {f g : Cot R' (CartierDual R' (R' ⊗[R] A)) →ₗ[R'] N}
    (h : ∀ φ : CartierDual R A, f (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      g (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) : f = g := by sorry
