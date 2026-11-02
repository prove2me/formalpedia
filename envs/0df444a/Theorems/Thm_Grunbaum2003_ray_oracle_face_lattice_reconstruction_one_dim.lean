-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_face_lattice_reconstruction_one_dim
-- name    : Grunbaum2003.ray_oracle_face_lattice_reconstruction_one_dim
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:08:14.096011+00:00
-- url     : https://prove2.me/theorems/7e409ae6-2ae4-4acd-8495-9b232bcdff63
-- title:
--   One-dimensional face-lattice reconstruction without ray queries
-- statement:
--   There is a single finite ray-machine program that works for every nonempty full-dimensional one-dimensional polytope and every oracle: starting from the zero configuration, it halts in finite time, makes zero oracle queries, and outputs the entire exposed-face lattice.
--
--   Every such polytope is a nondegenerate segment. Its face lattice has four elements: the empty face, its two vertices, and the whole segment. The output records this abstract inclusion order, so the program needs no endpoint coordinates. Oracle correctness and an interior-origin hypothesis are unnecessary for this one-dimensional case.
-- source:
--   One-dimensional base case of the Gritzmann–Klee–Westwater ray-oracle reconstruction theorem in Grünbaum (2003), Convex Polytopes, §3.6, printed pp.52b–52c/PDF74–75, with the exposed-face convention of §2.4. https://prove2.me/theorems/60ec78e9-77c6-458e-8d47-5b17e861648a

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
set_option autoImplicit false

namespace Grunbaum2003

theorem ray_oracle_face_lattice_reconstruction_one_dim :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin 1 → ℝ), IsDPolytope P →
        ∀ oracle : (Fin 1 → ℝ) → (Fin 1 → ℝ),
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧ c.queries = 0 ∧
            IsRayFaceLatticeOutput P c := by sorry

end Grunbaum2003
