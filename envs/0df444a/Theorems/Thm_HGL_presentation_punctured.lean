-- Prove2me | Theorems.Thm_HGL_presentation_punctured
-- name    : HGL.presentation_punctured
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:10:43.38951+00:00
-- url     : https://prove2.me/theorems/d2b08654-4b89-42da-b38b-fa8af2ecbbac
-- title:
--   The presentation of the link-homotopy classes over a punctured surface (Corollary 3.10)
-- statement:
--   Over the punctured surface, the class group admits the presentation with the generators a and sigma and the relations LH, R1, R2, R4, R5, and R6 - the relations of the closed-surface presentation with the surface relation R3 omitted, since the deleted point removes the relation involving the boundary word. The universal property: any group with a family of sigma elements and a family of a elements satisfying these relations receives a unique homomorphism from the class group mapping the standard generators to the families.
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Corollary 3.10).

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

namespace HGL

/-!  Milestone 7 (Corollary 3.10): the link-homotopy class group of a
punctured surface admits the presentation with the generators a_(1,r) and
sigma_i and the relations LH, R1, R2, R4, R5, R6 - the relations of
Theorem 3.9 with the surface relation R3 omitted, since the deleted point
removes the relation involving the boundary word. The universal property:
any group with families satisfying these relations receives a unique
homomorphism from the class group mapping the standard generators to the
families. -/
theorem presentation_punctured {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∀ (G : Type) [Group G] (sigma : Fin (n - 1) → G) (a : Fin (2 * g) → G),
      SatisfiesPuncturedPresentation W.hn sigma a →
      ∃! f : Cl →* G, (∀ i : Fin (n - 1), f (W.gen_sigma i) = sigma i) ∧
        (∀ r : Fin (2 * g), f (W.gen_a r) = a r) := by sorry

end HGL
