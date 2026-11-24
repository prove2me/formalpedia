-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryOrbitForm_dotProduct_star_eq_re
-- name    : GlobalTheory.UnitaryOrbitForm.dotProduct_star_eq_re
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:22.494803+00:00
-- url     : https://prove2.me/theorems/9d78082e-7c98-46a1-848a-b5796e9eb0c4
-- title:
--   Unitary Orbit Form: dot Product star eq re
-- statement:
--   The Unitary Orbit Form construction uses the dot Product star eq re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L56-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}

theorem GlobalTheory.UnitaryOrbitForm.dotProduct_star_eq_re {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian)
    (w : Fin r → ℂ) : w ⬝ᵥ A *ᵥ star w = ((w ⬝ᵥ A *ᵥ star w).re : ℂ) := by sorry
