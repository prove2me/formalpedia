-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_isGroupLikeElem_dual_iff
-- name    : GlobalTheory.CartierDual.isGroupLikeElem_dual_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:21.297802+00:00
-- url     : https://prove2.me/theorems/5fb4fdec-7416-485c-b402-02c1c6b8c8db
-- title:
--   Cartier Dual: is Group Like Elem dual iff
-- statement:
--   The Cartier Dual construction uses the is Group Like Elem dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L875-L879
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L875-L879

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

theorem GlobalTheory.CartierDual.isGroupLikeElem_dual_iff {R H : Type*} [CommSemiring R] [Semiring H] [Algebra R H]
    [Module.Finite R H] [Module.Projective R H] (φ : CartierDual R H) :
    IsGroupLikeElem R φ ↔ φ 1 = 1 ∧ ∀ a b, φ (a * b) = φ a * φ b := by sorry
