-- Prove2me | Theorems.Thm_Gerver_monotone_container
-- name    : Gerver.monotone_container
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-19T20:09:24.626633+00:00
-- url     : https://prove2.me/theorems/0c8b657d-8b18-4d93-be82-538bf4c779c8
-- title:
--   Every moving sofa sits in a monotone moving sofa
-- statement:
--   For every moving sofa S there is a moving sofa T that is monotone — an intersection of strips and hallways arising from a rotation path of some angle ω ∈ (0, π/2] — that contains S and has area at least the area of S. This is the reduction of the moving sofa problem to monotone sofas: the intersection I(S) of the supporting hallways of S is itself a moving sofa containing S, and area is monotone under inclusion.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Theorem 2.3.2 and Theorem 2.4.4 (Step 1-(a) of the proof outline)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 1a (Theorem 2.3.2 and Theorem 2.4.4): every moving sofa is contained
in a monotone moving sofa of at least its own area. The intersection I(S) of
the supporting hallways of S is a moving sofa that contains S, so a
maximum-area moving sofa can be assumed monotone. -/
theorem monotone_container (S : Set (ℝ × ℝ)) (hS : IsMovingSofa S) :
    ∃ T, IsMonotoneSofa T ∧ IsMovingSofa T ∧ S ⊆ T ∧ area S ≤ area T := by
  sorry

end Gerver
