-- Prove2me | Theorems.Thm_MasulloGRH_equicontinuous_of_le_continuous_seminorm
-- name    : MasulloGRH.equicontinuous_of_le_continuous_seminorm
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:12:48.970521+00:00
-- url     : https://prove2.me/theorems/6e2655f8-4e3d-495d-b794-0bba57cfaefb
-- title:
--   Linear functionals dominated by one continuous seminorm form an equicontinuous family
-- statement:
--   Let $F$ be a complex vector space with a locally convex topology, $r$ a continuous seminorm on $F$, and $(\psi_m)_{m\ge0}$ a sequence of linear functionals on $F$ such that
--
--   $$|\psi_m(y)|\le r(y)\qquad\text{for all }m\text{ and all }y\in F.$$
--
--   Then every $\psi_m$ is continuous, and the family $(\psi_m)_m$ is equicontinuous.
--
--   This is the elementary converse direction of the description of equicontinuous sets of functionals as those dominated by a single continuous seminorm.
--
--   **Formalization Note** The conclusion provides continuous linear functionals $\psi'_m$ (elements of `StrongDual ℂ F`) that agree pointwise with $\psi_m$ and whose underlying functions form an equicontinuous family.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.2.4.18 (Schwartz kernel theorem) and its proof; cf. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 50 (Theorem 50.1 and Proposition 50.5)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem equicontinuous_of_le_continuous_seminorm (F : Type*) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (hF : IsLocallyConvexTopology F ‹TopologicalSpace F›)
    (r : Seminorm ℂ F) (hr : Continuous r) (ψ : ℕ → F →ₗ[ℂ] ℂ) (hψ : ∀ m y, ‖ψ m y‖ ≤ r y) :
    ∃ ψ' : ℕ → StrongDual ℂ F, (∀ m y, ψ' m y = ψ m y) ∧
      Equicontinuous (fun m => (ψ' m : F → ℂ)) := by sorry

end MasulloGRH
