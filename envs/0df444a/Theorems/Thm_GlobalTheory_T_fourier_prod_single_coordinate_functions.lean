-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_prod_single_coordinate_functions
-- name    : GlobalTheory.T.fourier_prod_single_coordinate_functions
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:19.215182+00:00
-- url     : https://prove2.me/theorems/e0ab2940-1828-4be9-8c09-04f431e58d6f
-- title:
--   T: fourier prod single coordinate functions
-- statement:
--   The T construction uses the fourier prod single coordinate functions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierProdSingleCoordinateFunctionsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierProdSingleCoordinateFunctionsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctions
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctionsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fourier_prod_single_coordinate_functions : ∀ (I : Type) [Fintype I] (f : I → ℂ → ℂ), (∀ i, Integrable (f i)) → ∀ l : EuclideanSpace ℂ I, 𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by sorry
