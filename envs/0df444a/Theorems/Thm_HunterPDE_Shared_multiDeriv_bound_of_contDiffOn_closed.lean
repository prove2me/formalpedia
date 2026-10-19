-- Prove2me | Theorems.Thm_HunterPDE_Shared_multiDeriv_bound_of_contDiffOn_closed
-- name    : HunterPDE.Shared.multiDeriv_bound_of_contDiffOn_closed
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T16:37:03.952248+00:00
-- url     : https://prove2.me/theorems/5c73b783-6c45-4ce3-8b15-71176299f7d5
-- title:
--   Compact bounds for classical derivatives from smoothness on a closed set
-- statement:
--   Let S be a closed subset of Euclidean space with the unique differentiability property, Ω an open subset of S, and K a compact set. Suppose f is smooth on S and vanishes on Ω outside K. Then for every multi-index α there is a nonnegative real constant C such that, on Ω, the norm of ∂^α f is bounded by C times the indicator of K. Thus all interior derivatives vanish off K and are uniformly bounded even as points approach the boundary. The values of f outside S are arbitrary. This generalizes the compact derivative bound used for functions smooth up to the boundary of a half-space.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definitions 3.1–3.2 and discussion printed pp.47–48, Definition 3.23 printed p.58, smooth compact closed-half-space class in Theorem 3.42 printed p.72. General compactness formulation: iterate within-derivatives on a closed set of unique differentiability, restrict to the open interior, and bound the continuous derivative representatives on K ∩ S.

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open HunterPDE.Shared
open scoped ContDiff Topology
set_option autoImplicit false

theorem HunterPDE.Shared.multiDeriv_bound_of_contDiffOn_closed {n : ℕ} {S Ω K : Set (EuclideanSpace ℝ (Fin n))}
    (hS : IsClosed S) (hSd : UniqueDiffOn ℝ S) (hΩ : IsOpen Ω) (hΩS : Ω ⊆ S)
    (hK : IsCompact K) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ ∞ f S) (hz : ∀ x ∈ Ω, x ∉ K → f x = 0)
    (α : Fin n → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ω, ‖multiDeriv f α x‖ ≤ K.indicator (fun _ => C) x := by sorry
