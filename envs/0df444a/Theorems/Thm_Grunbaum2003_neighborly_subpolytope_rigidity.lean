-- Prove2me | Theorems.Thm_Grunbaum2003_neighborly_subpolytope_rigidity
-- name    : Grunbaum2003.neighborly_subpolytope_rigidity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:40:23.31993+00:00
-- url     : https://prove2.me/theorems/14803a33-3769-487e-b825-779377b57f23
-- title:
--   Shemer rigidity theorem — Reconstruction of all vertex subpolytopes
-- statement:
--   For positive even dimension, a vertex-preserving combinatorial equivalence between two neighborly polytopes induces a vertex-preserving combinatorial equivalence between every pair of corresponding vertex subpolytopes, including empty and lower-dimensional ones.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §7.5, Shemer rigidity theorem (unnumbered; cited as Shemer [a]), printed p. 129b / PDF p. 161; neighborliness conventions §§7.1–7.2, printed pp. 122–123 / PDF pp. 152–153; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsKNeighborly

set_option autoImplicit false

namespace Grunbaum2003

/-- Shemer's rigidity theorem as stated in Grünbaum (2003), §7.5,
"Cyclic polytopes", printed p.129b / PDF161. For positive even dimension,
the combinatorial type of a neighborly polytope determines the types of
all its vertex subpolytopes. The prescribed vertex correspondence is
retained for every subset, including lower-dimensional and empty ones.
The source's neighborly in dimension 2r means r-neighborly (§7.2).
This is combinatorial rigidity, not rigidity of lengths or realizations. -/
theorem neighborly_subpolytope_rigidity (r m : ℕ) (hr : 1 ≤ r)
    (P Q : Set (Fin (2 * r) → ℝ))
    (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hPn : IsKNeighborly r P) (hQn : IsKNeighborly r Q)
    (V W : Fin m → (Fin (2 * r) → ℝ))
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (θ : Equiv.Perm (Fin m)) (Φ : PolytopeFace P ≃o PolytopeFace Q)
    (hΦ : ∀ (i : Fin m) (F : PolytopeFace P),
      F.val = {V i} → (Φ F).val = {W (θ i)}) :
    ∀ I : Set (Fin m),
      ∃ Ψ : PolytopeFace (convexHull ℝ (V '' I)) ≃o
          PolytopeFace (convexHull ℝ (W '' (θ '' I))),
        ∀ (i : Fin m), i ∈ I →
          ∀ F : PolytopeFace (convexHull ℝ (V '' I)),
            F.val = {V i} → (Ψ F).val = {W (θ i)} := by sorry

end Grunbaum2003
