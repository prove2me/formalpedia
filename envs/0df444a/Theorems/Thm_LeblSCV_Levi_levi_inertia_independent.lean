-- Prove2me | Theorems.Thm_LeblSCV_Levi_levi_inertia_independent
-- name    : LeblSCV.Levi.levi_inertia_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:17:54.573982+00:00
-- url     : https://prove2.me/theorems/6077287e-da97-4516-8fc3-6ffb1100d263
-- title:
--   Proposition 2.3.6 — the inertia of the Levi form does not depend on the defining function
-- statement:
--   Let $U \subset \mathbb{C}^n$ be an open set with smooth boundary and $p \in \partial U$, and let $r$, $r'$ be two defining functions of $U$ at $p$, both negative on $U$. Then the Levi forms $\mathcal{L}_r$ and $\mathcal{L}_{r'}$ at $p$ have the same numbers of positive and of negative eigenvalues on $T^{(1,0)}_p\partial U$. Consequently
--   $$\mathcal{L}_r \ge 0 \text{ on } T^{(1,0)}_p\partial U \iff \mathcal{L}_{r'} \ge 0 \text{ on } T^{(1,0)}_p\partial U,$$
--   and likewise for positive definiteness: pseudoconvexity and strong pseudoconvexity at $p$ do not depend on the defining function.
--
--   **Formalization Note.** The inertia is recorded by `leviPosIndex` and `leviNegIndex`; each Levi form is taken on the holomorphic tangent space computed from its own defining function. The book leaves the proof as an exercise (Exercise 2.3.8).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 68, Proposition 2.3.6

import Mathlib
import Definitions.Def_LeblSCV_Levi_HasSmoothBoundary
import Definitions.Def_LeblSCV_Levi_holTangent
import Definitions.Def_LeblSCV_Levi_leviForm
import Definitions.Def_LeblSCV_Levi_leviPosIndex

namespace LeblSCV.Levi

/-- Proposition 2.3.6 (Lebl, p. 68): the inertia of the Levi form at `p ∈ ∂U` does not depend on
the defining function; hence neither do pseudoconvexity and strong pseudoconvexity at `p`. -/
theorem levi_inertia_independent {n : ℕ} (U : Set (Fin n → ℂ)) (hU : HasSmoothBoundary U)
    (p : Fin n → ℂ) (hp : p ∈ frontier U)
    (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ) (hr : IsDefiningFunction U p V r)
    (V' : Set (Fin n → ℂ)) (r' : (Fin n → ℂ) → ℝ) (hr' : IsDefiningFunction U p V' r') :
    leviPosIndex r p = leviPosIndex r' p ∧ leviNegIndex r p = leviNegIndex r' p ∧
      ((∀ a ∈ holTangent r p, 0 ≤ (leviForm r p a).re) ↔
        (∀ a ∈ holTangent r' p, 0 ≤ (leviForm r' p a).re)) ∧
      ((∀ a ∈ holTangent r p, a ≠ 0 → 0 < (leviForm r p a).re) ↔
        (∀ a ∈ holTangent r' p, a ≠ 0 → 0 < (leviForm r' p a).re)) := by sorry

end LeblSCV.Levi
