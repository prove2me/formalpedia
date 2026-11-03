-- Prove2me | Theorems.Thm_NearestDSM_lemma_3_12
-- name    : NearestDSM.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:57.968451+00:00
-- url     : https://prove2.me/theorems/535bb333-f681-46fa-b61f-60e54d0c7565
-- title:
--   Lemma 3.12 — every equivalence class has a vertex
-- statement:
--   Let $y\in\mathbb R^{2n-1}$. The polyhedron $[y]\subset\mathbb R^{2n-1}$ contains at least one vertex:
--   $$
--   \operatorname{ext}[y]\ne\emptyset .
--   $$
--   Step 3 of Algorithm 3.1 is therefore always possible.
--
--   Differences from the source:
--   - encoding: size $n\ge1$ → `n + 1`; vertex → extreme point; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 3.12, p.18

import Mathlib
import Definitions.Def_NearestDSM_equivClass

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 3.12, p.18. Let `y ∈ ℝ^{2n−1}`. The polyhedron `[y] ⊂ ℝ^{2n−1}`
contains at least one vertex.

**Formalization Note.** A vertex is an extreme point (`Set.extremePoints ℝ`). The paper's size
`n` is `n + 1`. -/
theorem lemma_3_12 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) :
    (Set.extremePoints ℝ (equivClass Xh y)).Nonempty := by sorry

end NearestDSM
