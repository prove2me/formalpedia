-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_ker_cotMap
-- name    : GlobalTheory.PDiv.ker_cotMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:34.373411+00:00
-- url     : https://prove2.me/theorems/074dcf16-6a1c-4898-894f-a2a23225c19c
-- title:
--   PDiv: ker cot Map
-- statement:
--   The PDiv construction uses the ker cot Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DUnitMemRangeOfMemKerIdeal.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DUnitMemRangeOfMemKerIdeal.lean#L62-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Coalgebra Bialgebra WithConv
open GlobalTheory
open GlobalTheory.PDiv
variable {R A C D : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing D]
  [Bialgebra R A] [Bialgebra R C] [Bialgebra R D]

theorem GlobalTheory.PDiv.ker_cotMap [IsCocomm R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) {m : ℕ}
    (hk : RingHom.ker f = torsionIdeal R C m) :
    LinearMap.ker (cotMap f) = Ideal.span {(m : R)} • (⊤ : Submodule R (Cot R C)) := by sorry
