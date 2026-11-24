-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_comul_eq_iff
-- name    : GlobalTheory.CartierDual.comul_eq_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:33.963928+00:00
-- url     : https://prove2.me/theorems/a3b7cf4f-43a6-497f-b534-4abd885c181c
-- title:
--   Cartier Dual: comul eq iff
-- statement:
--   The Cartier Dual construction uses the comul eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L159-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open GlobalTheory.CartierDual
variable {R H : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Module.Finite R H]
  [Module.Projective R H]

theorem GlobalTheory.CartierDual.comul_eq_iff (φ : CartierDual R H) (x : CartierDual R H ⊗[R] CartierDual R H) :
    comul φ = x ↔ ∀ a b, pair R H H x (a ⊗ₜ b) = φ (a * b) := by sorry
