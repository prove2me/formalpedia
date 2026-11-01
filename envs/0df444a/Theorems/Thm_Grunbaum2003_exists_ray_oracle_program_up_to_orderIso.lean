-- Prove2me | Theorems.Thm_Grunbaum2003_exists_ray_oracle_program_up_to_orderIso
-- name    : Grunbaum2003.exists_ray_oracle_program_up_to_orderIso
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:22:04.727422+00:00
-- url     : https://prove2.me/theorems/27497593-67bc-4d3e-9396-66515b6e7e96
-- title:
--   Gritzmann–Klee–Westwater ray-oracle reconstruction up to face-lattice order isomorphism
-- statement:
--   This lemma states the Gritzmann–Klee–Westwater ray-oracle reconstruction theorem up to combinatorial equivalence: for every dimension $d \ge 1$, there exists a ray-machine program $\Pi$ that, given ray-shooting oracle access to any $d$-polytope $P \subseteq \mathbb{R}^d$ with $0 \in \operatorname{int}(P)$, halts within the Gritzmann–Klee–Westwater query bound and outputs the face lattice of a model polytope $P'$ combinatorially equivalent to $P$.
--
--   Let $d \ge 1$ be a positive integer. Then there exists a program $\Pi : \operatorname{List} \operatorname{RayInstruction}$ such that for every $d$-polytope $P \subseteq \mathbb{R}^d$ with $0 \in \operatorname{int}(P)$ and every valid ray oracle $\mathcal{O} : \mathbb{R}^d \to \mathbb{R}^d$ (`IsPolytopeRayOracle P oracle`), there exist a step count $t \in \mathbb{N}$, a halting configuration $c$, and a subset $P' \subseteq \mathbb{R}^d$ satisfying
--
--   $$
--   c.\mathrm{queries} \le f_0(P) + (d - 1) f_{d-1}(P)^2 + (5d - 4) f_{d-1}(P),
--   $$
--
--   together with $\operatorname{IsRayFaceLatticeOutput}(P', c)$ and an order isomorphism $\mathcal{F}(P') \simeq_{\mathrm{ord}} \mathcal{F}(P)$.
--
--   By the combinatorial invariance theorem `rayMachine_halt_unique_and_output_iso_iff`, $\operatorname{IsRayFaceLatticeOutput}(P', c)$ and $\mathcal{F}(P') \simeq_{\mathrm{ord}} \mathcal{F}(P)$ imply $\operatorname{IsRayFaceLatticeOutput}(P, c)$, which immediately yields `ray_oracle_face_lattice_reconstruction`.
--
--   **Formalization Note** Decoupling the reconstructed face-lattice witness $P'$ from $P$ via $\mathcal{F}(P') \simeq_{\mathrm{ord}} \mathcal{F}(P)$ matches the fact that `IsRayFaceLatticeOutput` depends on $P$ only through the isomorphism type of its face poset `PolytopeFace P`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Order.Hom.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem exists_ray_oracle_program_up_to_orderIso (d : ℕ) (hd : 0 < d) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : RayConfiguration) (P' : Set (Fin d → ℝ)),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d - 1) * (faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * faceCount P (d - 1) ∧
            IsRayFaceLatticeOutput P' c ∧
            Nonempty (PolytopeFace P' ≃o PolytopeFace P) := by sorry

end Grunbaum2003
