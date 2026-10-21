-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_positive_compact_resolvent_realization
-- name    : HunterPDE.Elliptic.positive_compact_resolvent_realization
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T21:46:10.592264+00:00
-- url     : https://prove2.me/theorems/df29e783-1842-4479-a3ea-ab73c779a93d
-- title:
--   Positive compact Dirichlet resolvent and lifting its eigenvectors
-- statement:
--   Let Ω be bounded and open and let P be admissible and uniformly elliptic with vanishing first-order coefficients. There exist a real shift μ and a compact symmetric continuous linear operator K on L²(Ω), equal to the Dirichlet resolvent (L+μI)⁻¹, whose quadratic form is strictly positive on nonzero vectors. For every κ > 0 and every f satisfying Kf = κf, there is u in H¹₀(Ω) with L² class f and Lu = (1/κ−μ)u weakly against every H¹₀ test function. The zero vector is permitted. No spectral basis or ordering is assumed or concluded here. The analytic proof uses the proved energy, weak-existence and compact-resolvent milestones; density gives injectivity and the weak resolvent equation gives the eigenvector lift.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, sections 4.8–4.10, pp. 105–109, especially Theorem 4.25. https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf

import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

open MeasureTheory

theorem HunterPDE.Elliptic.positive_compact_resolvent_realization
    {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (P : HunterPDE.Elliptic.Coeffs n)
    (hP : P.Admissible Ω) (hb : P.b = 0) (hell : P.UniformlyElliptic Ω) :
    ∃ (μ : ℝ) (K : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω)),
      ⇑K = HunterPDE.Elliptic.resolvent Ω P μ ∧ IsCompactOperator K ∧
      (K : Lp ℝ 2 (volume.restrict Ω) →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω)).IsSymmetric ∧
      (∀ f, f ≠ 0 → 0 < inner ℝ (K f) f) ∧
      ∀ (κ : ℝ), 0 < κ → ∀ f : Lp ℝ 2 (volume.restrict Ω), K f = κ • f →
        ∃ u : HunterPDE.Elliptic.H10 n Ω, HunterPDE.Elliptic.toL2 u = f ∧
          HunterPDE.Elliptic.IsWeakSolution (HunterPDE.Elliptic.form P)
            (-(κ⁻¹ - μ)) (fun _ => 0) u := by sorry
