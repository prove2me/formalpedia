-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_norm_primitiveRoot_sub_one
-- name    : GlobalTheory.Cyc.norm_primitiveRoot_sub_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:57.564058+00:00
-- url     : https://prove2.me/theorems/66c33042-0210-4592-a130-72dca36896ab
-- title:
--   Cyc: norm primitive Root sub one
-- statement:
--   The Cyc construction uses the norm primitive Root sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPrimitiveRootPrimePowSubOnePadicComplex.lean#L34-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPrimitiveRootPrimePowSubOnePadicComplex.lean#L34-L60

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc

theorem GlobalTheory.Cyc.norm_primitiveRoot_sub_one (l : ℕ) [hl : Fact l.Prime] (j : ℕ)
    (hj : 1 ≤ j) (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by sorry
