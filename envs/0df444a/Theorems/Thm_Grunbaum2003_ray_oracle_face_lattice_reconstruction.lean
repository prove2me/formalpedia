-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_face_lattice_reconstruction
-- name    : Grunbaum2003.ray_oracle_face_lattice_reconstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:36:42.119331+00:00
-- url     : https://prove2.me/theorems/60ec78e9-77c6-458e-8d47-5b17e861648a
-- title:
--   Gritzmann–Klee–Westwater theorem — ray-oracle face-lattice reconstruction
-- statement:
--   For each positive dimension, one exact real ray-oracle program reconstructs the complete face lattice of every d-polytope containing the origin in its interior using at most f₀(P) + (d − 1) f_{d−1}(P)² + (5d − 4) f_{d−1}(P) ray queries.
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

theorem ray_oracle_face_lattice_reconstruction (d : ℕ) (hd : 0 < d) :
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
