-- Prove2me | Theorems.Thm_Grunbaum2003_centrally_symmetric_neighborly_families
-- name    : Grunbaum2003.centrally_symmetric_neighborly_families
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:40:43.104849+00:00
-- url     : https://prove2.me/theorems/c1a7d1e2-5aba-4b31-b2a8-c3e6b0ea1654
-- title:
--   Zaks theorem — Unbounded centrally symmetric neighborly families
-- statement:
--   For every integer dimension d at least three and every finite size threshold, there is a family meeting that threshold whose members are centrally symmetric full-dimensional convex d-polytopes in real d-space and whose every two distinct members intersect in affine dimension d minus one.
-- source:
--   Joseph Zaks, “Arbitrarily large neighborly families of symmetric convex polytopes,” Geometriae Dedicata 20 (1986), 175–179, DOI 10.1007/BF00164398; cited in Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §7.5, unnumbered Zaks [a] theorem, printed p. 129b / PDF p. 161; neighborly-family definition §7.4, printed p. 128 / PDF p. 158; central symmetry §6.4, printed pp. 114–115 / PDF pp. 142–143; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

set_option autoImplicit false

namespace Grunbaum2003

/-- Zaks's unbounded neighborly-family theorem, Grünbaum (2003), §7.5,
printed p.129b / PDF161. Neighborly families are defined in §7.4,
p.128 / PDF158: distinct members intersect in dimension d−1.
Central symmetry (§6.4, p.114 / PDF142) is invariance under reflection
about an individually chosen center, not a common center for the family.
A finite set records distinct polytopes; arbitrary lower bounds on its
cardinality express "arbitrarily large". Nonempty intersections avoid
the natural-valued affine dimension convention for the empty set.
This is the full family-existence capstone, with statement-only proof. -/
theorem centrally_symmetric_neighborly_families (d : ℕ) (hd : 3 ≤ d) (N : ℕ) :
    ∃ S : Finset (Set (Fin d → ℝ)),
      N ≤ S.card ∧
      (∀ P ∈ S, IsDPolytope P ∧
        ∃ c : Fin d → ℝ, (AffineEquiv.pointReflection ℝ c) '' P = P) ∧
      (∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
        (P ∩ Q).Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ (P ∩ Q)).direction + 1 = d) := by sorry

end Grunbaum2003
