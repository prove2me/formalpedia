-- Prove2me | Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_integral_mul_normalJetVanishing
-- name    : HunterPDE.Shared.HasWeakDeriv.integral_mul_normalJetVanishing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T13:27:05.113698+00:00
-- url     : https://prove2.me/theorems/fa50073d-46be-458e-8306-9f11bfeb85cd
-- title:
--   Weak integration by parts for tests with vanishing normal boundary jets
-- statement:
--   Let H be an open coordinate half-space, and suppose f and its specified weak multi-derivative g are locally integrable with respect to the restriction of volume to H, including on compact sets meeting the boundary. If a globally smooth compactly supported test has all normal derivatives of orders strictly below the normal order of the specified multi-index equal to zero on the boundary hyperplane, then the weak integration-by-parts identity remains valid with this test. No conditions are imposed on other weak derivatives of f. When the normal order is zero, no boundary conditions are required. A proposed proof multiplies the test by interior normal cutoffs; Taylor vanishing controls every Leibniz error in a shrinking strip, and local integrability gives convergence. This general higher-order cutoff result is an Open proof obligation.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A (March 19, 2024), Proposition 11.13, proof Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Independent analytic and calculus interfaces for the distributional justification; the weak-data boundary step is an additional cutoff argument, not attributed to the smooth calculation alone.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
open MeasureTheory HunterPDE.Shared
set_option autoImplicit false

theorem HunterPDE.Shared.HasWeakDeriv.integral_mul_normalJetVanishing
    {n : ℕ} (i : Fin n) (α : Fin n → ℕ)
    (f g ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict {x | 0 < x i}))
    (hg : LocallyIntegrable g (volume.restrict {x | 0 < x i}))
    (hd : HasWeakDeriv {x | 0 < x i} α f g)
    (hψ : IsTestFunction Set.univ ψ)
    (hb : ∀ r : ℕ, r < α i → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0) :
    (∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i}, g x * ψ x) =
      (-1 : ℝ) ^ (∑ k, α k) *
        ∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i}, f x * multiDeriv ψ α x := by sorry
