-- Prove2me | Theorems.Thm_HunterPDE_Shared_IsTestFunction_exists_boundaryCompatible_approx
-- name    : HunterPDE.Shared.IsTestFunction.exists_boundaryCompatible_approx
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T07:49:21.070792+00:00
-- url     : https://prove2.me/theorems/dcd53d5b-0e1c-4ad3-baa1-7da69433d39a
-- title:
--   Bounded interior approximation of boundary-compatible half-space tests
-- statement:
--   Let H be the open upper half-space in real Euclidean space, and let ψ be an ambient smooth compactly supported function. Fix a coordinate i; if i is normal to the boundary, assume ψ vanishes on the boundary hyperplane. Then there exist a compact set K, a nonnegative constant C, and smooth test functions φₙ compactly supported strictly inside H such that both |φₙ| and |∂ᵢφₙ| are bounded by C times the indicator of K, uniformly in n. At every point of H, φₙ converges to ψ and ∂ᵢφₙ converges to ∂ᵢψ. This is an elementary smooth approximation assertion, independent of weak derivatives and of any integration weights. A construction is φₙ(x)=χ((n+1)t)ψ(x), where χ vanishes for t≤1 and equals one for t≥2. In the normal case boundary vanishing bounds the extra derivative term uniformly.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised June 18, 2014, section 3.9, printed pp. 71–72, reflection construction preceding Theorem 3.41, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf . Auxiliary smooth-cutoff approximation derived to justify the reflection construction, not a separately numbered source theorem.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.Topology.Algebra.Order.Field

open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

theorem HunterPDE.Shared.IsTestFunction.exists_boundaryCompatible_approx
    (m : ℕ) (i : Fin (m + 1)) (ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hψ : HunterPDE.Shared.IsTestFunction Set.univ ψ)
    (hb : i = Fin.last m → ∀ x, x (Fin.last m) = 0 → ψ x = 0) :
    ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ φ : ℕ → EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
          (∀ n, HunterPDE.Shared.IsTestFunction (HunterPDE.Compactness.upperHalfSpace m) (φ n)) ∧
          (∀ n x, ‖φ n x‖ ≤ K.indicator (fun _ => C) x ∧
            ‖HunterPDE.Shared.multiDeriv (φ n) (Pi.single i 1) x‖ ≤
              K.indicator (fun _ => C) x) ∧
          (∀ x ∈ HunterPDE.Compactness.upperHalfSpace m,
            Tendsto (fun n => φ n x) atTop (𝓝 (ψ x)) ∧
            Tendsto (fun n => HunterPDE.Shared.multiDeriv (φ n) (Pi.single i 1) x)
              atTop (𝓝 (HunterPDE.Shared.multiDeriv ψ (Pi.single i 1) x))) := by sorry
