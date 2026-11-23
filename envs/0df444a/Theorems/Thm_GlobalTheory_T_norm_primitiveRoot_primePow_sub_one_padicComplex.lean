-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_primitiveRoot_primePow_sub_one_padicComplex
-- name    : GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:31.225841+00:00
-- url     : https://prove2.me/theorems/f34cf2a3-e222-4d11-a7c6-2fc1a59b3e42
-- title:
--   T: norm primitive Root prime Pow sub one padic Complex
-- statement:
--   The T construction uses the norm primitive Root prime Pow sub one padic Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPrimitiveRootPrimePowSubOnePadicComplexStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPrimitiveRootPrimePowSubOnePadicComplexStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), 1 ≤ j → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ (l ^ j) → ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by sorry
