-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_hyperplane_incidence_and_inclusion_table_programs
-- name    : Grunbaum2003.rayMachine_hyperplane_incidence_and_inclusion_table_programs
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T03:24:20.201889+00:00
-- url     : https://prove2.me/theorems/6984ffff-e8ad-4d5a-b984-a0f81a36efb6
-- title:
--   Compiled ray-machine programs for hyperplane vertex-facet incidence testing and $0/1$ subset-inclusion table emission
-- statement:
--   This theorem compiles the two output-synthesis components of the Gritzmann–Klee–Westwater ray-oracle reconstruction algorithm into verified `List RayInstruction` programs with zero oracle queries:
--   1. **Hyperplane Incidence Indicator (`hyperplaneIncidenceProgram`):** Given a $d$-dimensional functional $L$ at `lBase` and a point $x$ at `xBase`, evaluates the affine slack $\sum_{i=0}^{d-1} L_i x_i - 1$ and applies a 2-step 3-way `.branch` zero-indicator to write `1` if $\langle L, x \rangle = 1$ and `0` otherwise into `outBase ≥ minBase`, preserving all cells `< outBase`.
--   2. **Unary Header and $n \times n$ Subset-Inclusion Table Emitter (`headerAndInclusionTableProgram`):** Given an $n \times V$ matrix of $0/1$ face-vertex incidence bits stored at `fvBase + i * V + k`, evaluates the division-free boolean implication product $\prod_{k=0}^{V-1} (1 - I_{i,k}(1 - I_{j,k}))$ to emit the unary header `1, ..., 1, 0` of length $n + 1$ followed by the $n \times n$ $0/1$ subset-inclusion table into `outBase ..` and shifts the head to `outBase`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

theorem rayMachine_hyperplane_incidence_and_inclusion_table_programs :
  ∃ (hyperplaneIncidenceProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (hyperplaneIncidenceDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (hyperplaneIncidenceSteps : ℕ → ℤ → ℤ → ℕ)
    (headerAndInclusionTableProgram : ℕ → ℕ → ℤ → ℤ → List RayInstruction)
    (headerAndInclusionTableDest : ℕ → ℕ → ℤ → ℤ → ℤ)
    (headerAndInclusionTableSteps : ℕ → ℕ → ℤ → ℕ),
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := hyperplaneIncidenceProgram d lBase xBase minBase
      let outBase := hyperplaneIncidenceDest d lBase xBase minBase
      let steps := hyperplaneIncidenceSteps d lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps + 1 ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        c'.tape outBase =
          (if (∑ i : Fin d, source (lBase + (i.val : ℤ)) * source (xBase + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ {d n V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (fvBase minBase : ℤ) (q : ℕ) (inc : Fin n → Fin V → Prop),
      (∀ (a : Fin n) (k : Fin V),
        source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if inc a k then (1 : ℝ) else 0) →
      let prog := headerAndInclusionTableProgram n V fvBase minBase
      let outBase := headerAndInclusionTableDest n V fvBase minBase
      let steps := headerAndInclusionTableSteps n V fvBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = outBase ∧ c'.queries = q ∧
        (∀ i : Fin n, c'.tape (c'.head + (i.val : ℤ)) = 1) ∧
        c'.tape (c'.head + (n : ℤ)) = 0 ∧
        (∀ i j : Fin n,
          c'.tape (c'.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
            if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < c'.head → c'.tape z = source z)) := by sorry

end Grunbaum2003
