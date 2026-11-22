-- Prove2me | Theorems.Thm_HardyFLocal_regional_outcome_summability
-- name    : HardyFLocal.regional_outcome_summability
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:53:00.2311+00:00
-- url     : https://prove2.me/theorems/de45894e-b382-423f-9612-4e89e883a0fb
-- title:
--   Summability of clumped response vectors on arbitrary regions
-- statement:
--   For disjoint regions and fixed settings of the second region, the clumped response vectors are summable over all joint outcomes. The result includes boundary regions and arbitrary fiducial label choices.
-- source:
--   Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054, sections 4.4 and 5.

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_elementary_coordinates_summable
open HardyCausaloid
open Classical

namespace HardyFLocal

open Classical in
theorem regional_outcome_summability {m n : ℕ} (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    {O₁ O₂ : Finset (X m n)} (h : Disjoint O₁ O₂)
    (α : Lab (Setting m n) (Outcome m n) O₁)
    (F : ∀ x : O₂, Setting m n x.1) :
    Summable fun y : O₂ → ℕ => (actualCausaloid S L).r (O₁ ∪ O₂) (joinLab α (labOf F y)) := by sorry

end HardyFLocal
