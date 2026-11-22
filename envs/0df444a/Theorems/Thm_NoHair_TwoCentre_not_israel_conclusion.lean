-- Prove2me | Theorems.Thm_NoHair_TwoCentre_not_israel_conclusion
-- name    : NoHair.TwoCentre.not_israel_conclusion
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:23:05.849866+00:00
-- url     : https://prove2.me/theorems/8dd49003-60bb-49a3-ae6d-a0ae29895f25
-- title:
--   The two-centre Faraday field excludes a Reissner–Nordström exterior
-- statement:
--   Let $D$ be an open region in a smooth four-manifold equipped with bilinear fields $g$ and $F$. Suppose a diffeomorphism from the full two-centre isotropic exterior onto $D$ pulls $F$ back to the equal-mass Majumdar–Papapetrou Faraday tensor, with the centres at $(-1,0,0)$ and $(1,0,0)$.
--
--   Then $D$ cannot satisfy the Reissner–Nordström conclusion in the Israel electrovacuum milestone, for any admissible mass, charge, or choice of constant duality rotation:
--
--   $$
--   \neg\exists m,e,\quad \mathrm{BHParams}(m,0,e)\ \land\ \mathrm{IsKerrNewmanDOC}(g,F,D;m,0,e).
--   $$
--
--   The statement addresses the exterior field. Realizing $D$ as the domain of outer communications of a spacetime satisfying all of the milestone's hypotheses is a further geometric obligation.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. H. S. Reall, Part III Black Holes (2024), §6.1, equations (6.2)–(6.6), https://www.damtp.cam.ac.uk/user/hsr1000/black_holes_lectures_2024.pdf.

import Definitions.Def_NoHair_TwoCentre
import Definitions.Def_NoHair_spacetime

open NoHair NoHair.TwoCentre Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.not_israel_conclusion {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (D : Set M)
    (hD : IsOpen D) (Ψ : E4 → M) (hΨ : IsDiffeoOnto Ψ exterior D)
    (hfield : ∀ y ∈ exterior, pullbackCoeffs F Ψ y = field y) :
    ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧ IsKerrNewmanDOC g F D m 0 e := by
  sorry
