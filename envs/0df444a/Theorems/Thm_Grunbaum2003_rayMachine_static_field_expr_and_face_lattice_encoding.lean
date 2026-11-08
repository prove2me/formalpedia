-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_static_field_expr_and_face_lattice_encoding
-- name    : Grunbaum2003.rayMachine_static_field_expr_and_face_lattice_encoding
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:23.462868+00:00
-- url     : https://prove2.me/theorems/1099dffb-0672-41f0-842f-b86f36af5079
-- title:
--   Static field-expression ray-machine compiler and exposed-vertex subset characterization of face-lattice output
-- statement:
--   This theorem establishes two foundational components for the final synthesis phase of Gritzmann–Klee–Westwater ray-oracle face-lattice reconstruction:
--   1. **Static field-expression compilation and additive run composition (`RayFieldExpr`):** `rayMachineRun` composes additively over step counts (`run_add`), and any rational/field expression tree (`const`, `read`, `add`, `sub`, `mul`, `div`) over input tape cells below a fresh scratch base `base` compiles via `Expr.emit base pc` into a straight-line `List RayInstruction` block that executes in `e.steps` steps with zero oracle queries, writes `e.eval source` to `tape base`, and preserves every tape cell outside `[base, base + e.slots)`.
--   2. **Exposed-vertex subset characterization of `PolytopeFace P` and `IsRayFaceLatticeOutput P c`:** Under the exposed-vertex hull representation $E = \operatorname{conv}(E \cap \operatorname{vert}(P))$, two exposed faces $E_1, E_2 \in \operatorname{PolytopeFace} P$ satisfy $E_1 \le E_2$ if and only if $E_1 \cap \operatorname{vert}(P) \subseteq E_2 \cap \operatorname{vert}(P)$, `PolytopeFace P` is finite (`∃ n, Nonempty (Fin n ≃ PolytopeFace P)`), and writing the unary length header followed by the $0/1$ vertex-subset inclusion table produces a valid `IsRayFaceLatticeOutput P c`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finite.Set

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

theorem rayMachine_static_field_expr_and_face_lattice_encoding :
  (∃ (run_add : ∀ {d : ℕ} (program : List RayInstruction)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
        rayMachineRun program oracle (a + b) c =
          (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
     (standalone_add_sub_mul_div_step :
        ∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ) (base a b : ℤ) (q : ℕ),
          a < base → b < base →
          ∃ c' : RayConfiguration,
            rayMachineRun
              ([.constant base 0 1, .add base a base 2,
                .constant (base + 1) 0 3, .add (base + 1) b (base + 1) 4,
                .add base base (base + 1) 5, .halt])
              oracle 5 ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = 5 ∧ c'.head = 0 ∧ c'.queries = q ∧
            c'.tape base = source a + source b ∧
            ∀ z : ℤ, (z < base ∨ base + 2 ≤ z) → c'.tape z = source z),
     True) ∧
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      (∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      (∀ E₁ E₂ : PolytopeFace P,
        E₁ ≤ E₂ ↔ ∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ E₁.val → x ∈ E₂.val) ∧
      ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite →
        ∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) ∧
      (∀ {n : ℕ} (e : Fin n ≃ PolytopeFace P) (c : RayConfiguration),
        (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) →
        c.tape (c.head + (n : ℤ)) = 0 →
        (∀ i j : Fin n,
          c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
            if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val) then 1 else 0) →
        IsRayFaceLatticeOutput P c)) := by sorry

end Grunbaum2003
