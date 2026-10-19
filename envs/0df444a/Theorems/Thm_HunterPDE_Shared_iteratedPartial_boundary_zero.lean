-- Prove2me | Theorems.Thm_HunterPDE_Shared_iteratedPartial_boundary_zero
-- name    : HunterPDE.Shared.iteratedPartial_boundary_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T19:38:11.250087+00:00
-- url     : https://prove2.me/theorems/7b746329-d801-4460-b9a0-60c9b98feb4d
-- title:
--   Vanishing normal boundary jets imply vanishing mixed boundary derivatives
-- statement:
--   Let $f$ be smooth on Euclidean space, with all pure normal derivatives of orders less than $k$ vanishing on $x_i=0$. For every finite word of coordinate derivatives containing fewer than $k$ occurrences of $i$, its iterated derivative also vanishes on that hyperplane. Tangential derivatives have arbitrary order. No support or integrability assumption is needed.
-- source:
--   Derived smooth hyperplane calculus lemma. Commute mixed derivatives using HunterPDE.Shared.iteratedPartial_eq_of_perm (Hunter, Notes on Partial Differential Equations, Section 1.8 and Theorem 1.27, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf); differentiate the identically zero restriction along tangential lines using the chain rule. This precise boundary-jet interface is derived, not a verbatim numbered source assertion.

import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.iteratedPartial_boundary_zero {n : ℕ} (i : Fin n) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ r : ℕ, r < k → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial f (List.replicate r i) x = 0)
    (l : List (Fin n)) (hl : l.count i < k) :
    ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 → iteratedPartial f l x = 0 := by sorry
