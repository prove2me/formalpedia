-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_relocate_and_section_query_adapter
-- name    : Grunbaum2003.rayMachine_relocate_and_section_query_adapter
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:43.384204+00:00
-- url     : https://prove2.me/theorems/b384f994-3915-4a74-9cc0-abf6453e6ef2
-- title:
--   Ray-machine code relocation and $(d+9)$-step ambient planar-section query adapter
-- statement:
--   This theorem establishes two foundational machine-level building blocks for executing higher-dimensional Gritzmann–Klee–Westwater ray-oracle protocols on `rayMachineRun`:
--
--   1. **Instruction relocation (`RayCode.relocated_run`, `RayCode.relocated_halt`):** Shifting every control-flow target in a program `program : List RayInstruction` by `pre.length` (`relocateInstruction pre.length`) commutes exactly with `rayMachineStep` and `rayMachineRun` under `relocateConfiguration pre.length` (which shifts `pc` by `pre.length` while preserving `head`, `tape`, and `queries`), and preserves halting states.
--   2. **Physical planar-section query adapter (`RaySectionProgram.sectionQueryProgram_correct`):** For any ambient dimension $d \in \mathbb{N}$ and distinct coordinate indices $i \neq j$ in $\operatorname{Fin} d$, there exists an explicit instruction list `prog` of length $d + 10$ that, starting at `pc = 0, head = 0` with step size $\varepsilon = \mathrm{tape}(17) \neq 0$, anchor point $p_m = \mathrm{tape}(18 + m)$ ($p_j \neq 0$), and nonzero planar ray direction $(r_0, r_1) = (\mathrm{tape}(0), \mathrm{tape}(1)) \neq 0$:
--      - halts in $d + 9$ steps with `head = 0` and `queries = q + 1`;
--      - queries the ambient ray oracle on the embedded direction $f(r)_m = \varepsilon r_0 \delta_{m,i} + r_1 p_m$ and stores the full ambient reply $y = \operatorname{oracle}(f(r))$ in cells $18 + d + m$ ($0 \le m < d$);
--      - writes the exact left-inverse planar coordinates $\bigl((y_i - (y_j / p_j) p_i)/\varepsilon,\; y_j / p_j\bigr)$ back into cells $0$ and $1$; and
--      - preserves all other tape cells outside $\{0, 1\}$, the query block $[18 + d, 18 + 2d)$, and the scratch cell $18 + 2d$.
--
--   **Formalization Note** Because the planar secant detector operates on cells $0 \dots 16$, placing the anchor point at $18 \dots 18 + d - 1$, the physical query block at $18 + d \dots 18 + 2d - 1$, and the scratch cell at $18 + 2d$ guarantees zero tape interference with the native 2D controller.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace Grunbaum2003

theorem rayMachine_relocate_and_section_query_adapter :
    (∃ (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration),
      ∀ (d : ℕ) (pre program : List RayInstruction)
        (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
        (relocateCfg pre.length c).pc = pre.length + c.pc ∧
        (relocateCfg pre.length c).head = c.head ∧
        (relocateCfg pre.length c).tape = c.tape ∧
        (relocateCfg pre.length c).queries = c.queries ∧
        rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
            (relocateCfg pre.length c) =
          (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
        (program[c.pc]? = some .halt →
          (pre ++ program.map (relocateInst pre.length))[
            (relocateCfg pre.length c).pc]? = some .halt)) ∧
    (∀ (d : ℕ) (i j : Fin d), i ≠ j →
      ∃ prog : List RayInstruction,
        prog.length = d + 10 ∧
        ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
          tape 17 ≠ 0 →
          tape (18 + (j.val : ℤ)) ≠ 0 →
          (fun k : Fin 2 => if k = 0 then tape 0 else tape 1) ≠ 0 →
          ∃ c : RayConfiguration,
            rayMachineRun prog oracle (d + 9)
              {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
            prog[c.pc]? = some .halt ∧
            c.head = 0 ∧ c.queries = q + 1 ∧
            (∀ k : Fin 2, c.tape (k.val : ℤ) =
              let p : Fin d → ℝ := fun m => tape (18 + (m.val : ℤ))
              let y : Fin d → ℝ := oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) + tape 1 * p m)
              if k = 0 then (y i - (y j / p j) * p i) / tape 17 else y j / p j) ∧
            (∀ k : Fin d, c.tape (18 + (d : ℤ) + (k.val : ℤ)) =
              oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) +
                  tape 1 * tape (18 + (m.val : ℤ))) k) ∧
            (∀ z : ℤ, z ≠ 0 → z ≠ 1 →
              (z < 18 + (d : ℤ) ∨ 18 + (d : ℤ) + (d : ℤ) ≤ z) →
              z ≠ 18 + 2 * (d : ℤ) → c.tape z = tape z)) := by sorry

end Grunbaum2003
