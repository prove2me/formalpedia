-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_face_lattice_reconstruction_ge_two
-- name    : Grunbaum2003.ray_oracle_face_lattice_reconstruction_ge_two
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-01T18:09:52.540953+00:00
-- url     : https://prove2.me/theorems/a3a69631-8d08-46a3-87dd-be2991739552
-- title:
--   Ray-oracle face-lattice reconstruction in dimensions at least two
-- statement:
--   For every fixed dimension $d\ge2$, there exists one exact-real ray-machine program that works uniformly for all full-dimensional nonempty $d$-polytopes $P\subseteq\mathbb R^d$ containing the origin in their interior. Given any ray oracle that returns a positive intersection with the boundary of $P$ in each nonzero direction, the program halts with an encoding of the entire face lattice of $P$ and makes at most
--
--   $$
--   f_0(P)+(d-1)f_{d-1}(P)^2+(5d-4)f_{d-1}(P)
--   $$
--
--   oracle queries. The program depends only on $d$, not on the particular polytope or oracle. The output lists a finite set of faces and its complete inclusion relation, up to a bijective enumeration of all exposed faces including the empty and full faces.
--
--   This is the dimension-at-least-two case of the Gritzmann–Klee–Westwater reconstruction theorem. The one-dimensional case has a separate constant-output proof and uses no oracle queries.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.6, unnumbered Gritzmann–Klee–Westwater theorem, printed pp. 52b–52c / PDF pp. 74–75; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem ray_oracle_face_lattice_reconstruction_ge_two (d : ℕ) (hd : 2 ≤ d) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d - 1) * (faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * faceCount P (d - 1) ∧
            IsRayFaceLatticeOutput P c := by sorry

end Grunbaum2003
