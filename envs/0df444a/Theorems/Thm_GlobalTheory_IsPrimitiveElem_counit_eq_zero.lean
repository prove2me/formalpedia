-- Prove2me | Theorems.Thm_GlobalTheory_IsPrimitiveElem_counit_eq_zero
-- name    : GlobalTheory.IsPrimitiveElem.counit_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:13.382616+00:00
-- url     : https://prove2.me/theorems/f591819f-5c76-4d06-af70-fcb329467694
-- title:
--   Is Primitive Elem: counit eq zero
-- statement:
--   The Is Primitive Elem construction uses the counit eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L969-L973
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L969-L973

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

theorem GlobalTheory.IsPrimitiveElem.counit_eq_zero {R H : Type*} [CommRing R] [Semiring H] [Bialgebra R H]
    {a : H} (ha : IsPrimitiveElem R a) : counit (R := R) a = 0 := by sorry
