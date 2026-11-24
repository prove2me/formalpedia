-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_counit_addMonoidAlgebra
-- name    : GlobalTheory.CartierDual.counit_addMonoidAlgebra
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:48.020009+00:00
-- url     : https://prove2.me/theorems/4d888608-25f9-447a-bc67-96b6f63431d0
-- title:
--   Cartier Dual: counit add Monoid Algebra
-- statement:
--   The Cartier Dual construction uses the counit add Monoid Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1136-L1139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1136-L1139

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
variable (R Γ : Type*) [CommSemiring R]
variable {R Γ}

theorem GlobalTheory.CartierDual.counit_addMonoidAlgebra [AddMonoid Γ] [Finite Γ]
    (φ : CartierDual R (AddMonoidAlgebra R Γ)) :
    counit (R := R) φ = addMonoidAlgebraEquiv R Γ φ 0 := by sorry
