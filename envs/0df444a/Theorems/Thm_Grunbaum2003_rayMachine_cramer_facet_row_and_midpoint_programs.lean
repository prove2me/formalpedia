-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_cramer_facet_row_and_midpoint_programs
-- name    : Grunbaum2003.rayMachine_cramer_facet_row_and_midpoint_programs
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:55:44.158211+00:00
-- url     : https://prove2.me/theorems/beb905f1-bf45-4a2f-b684-cd0da93ec735
-- title:
--   Compiled straight-line ray-machine programs for $d \times d$ Cramer facet-normal coefficients and frame-extension midpoints
-- statement:
--   This theorem compiles two core linear-algebraic and geometric subroutines of the Gritzmann–Klee–Westwater ray-oracle reconstruction algorithm into verified straight-line `List RayInstruction` programs:
--   1. **Cramer Facet-Normal Solver (`cramerRowProgram`):** Given a $d \times d$ matrix $v$ of boundary points stored row-major on the tape at `vBase + i * d + j` with $\det(v) \ne 0$, `cramerRowProgram d vBase minBase` executes in `cramerRowSteps d vBase` steps with `0` oracle queries, never divides by zero, writes all $d$ Cramer facet-normal coefficients $(v.\text{updateCol } k (\text{fun } \_ \Rightarrow 1)).\det / v.\det$ ($k \in \operatorname{Fin} d$) into `outBase .. outBase + (d - 1)` (`outBase ≥ minBase`), and preserves all tape cells strictly below `outBase`.
--   2. **Frame-Extension Midpoint (`midpointVecProgram`):** Given two $d$-vectors $p, q$ stored at `pBase` and `qBase`, `midpointVecProgram d pBase qBase minBase` writes all $d$ coordinates $(p_i + q_i) / 2$ of the midpoint $\frac{1}{2}(p + q)$ into `outBase .. outBase + (d - 1)` in `0` oracle queries while preserving all tape cells strictly below `outBase`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem rayMachine_cramer_facet_row_and_midpoint_programs :
  ∃ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ),
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) := by sorry

end Grunbaum2003
