-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_inner_simplex_and_signed_direction_program
-- name    : Grunbaum2003.rayMachine_inner_simplex_and_signed_direction_program
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:16.777163+00:00
-- url     : https://prove2.me/theorems/e3332906-691f-4c76-8227-4826cf03ceed
-- title:
--   Inner-simplex ray-oracle sampling program and two-sided directional points in $P$
-- statement:
--   This theorem formalizes the $(d+1)$-query inner-simplex initialization of the Gritzmann–Klee–Westwater ray-oracle reconstruction algorithm on `rayMachineRun`, together with its geometric guarantee of explicit two-sided feasible points along every direction $u \in \mathbb{R}^d$.
--
--   Specifically, for any ambient dimension $d \ge 1$, any $d$-polytope $P \subseteq \mathbb{R}^d$ (`IsDPolytope P`), and any ray oracle `oracle` (`IsPolytopeRayOracle P oracle`):
--   1. **Two-sided feasible directional scale (`rayOracle_signed_inner_points`):** Querying the $d$ standard coordinate axes $e_i$ (yielding positive boundary scales $t_i = \operatorname{oracle}(e_i)_i > 0$) and the negative all-ones ray $-\mathbf{1} = (-1, \dots, -1)$ (yielding $s = -\operatorname{oracle}(-\mathbf{1})_0 > 0$) defines the field-arithmetic uniform axis scale
--      $$
--      a_0 = \Bigl(1 + s^{-1} + \sum_{i=0}^{d-1} t_i^{-1}\Bigr)^{-1} > 0
--      $$
--      and, for every direction $u \in \mathbb{R}^d$, the directional radius $a(u) = \frac{a_0}{1 + \sum_i |u_i|} > 0$ satisfying $-a(u) u \in P$ and $a(u) u \in P$.
--   2. **Literal unrolled initialization program (`innerSampleProgram_correct`, `stored_scales`):** The instruction list `innerSampleProgram d : List RayInstruction` executes in $(d+1)(d+2) + 2$ steps from `{pc := 0, head := 0, tape := tape, queries := q}`, halts at `pc = (d+1)(d+2) + 2` with `head = 0` and `queries = q + (d + 1)`, stores the $d+1$ oracle replies in disjoint blocks `[(i+1)d, (i+2)d)`, preserves all tape cells outside `[d, (d+2)d)`, and places $t_i$ at cell $(i+1)d + i$ and $-s$ at cell $(d+1)d$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem rayMachine_inner_simplex_and_signed_direction_program :
    ∃ (axis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (negativeDirection : ∀ d : ℕ, Fin d → ℝ)
      (positiveScale : ∀ {d : ℕ}, ((Fin d → ℝ) → Fin d → ℝ) → Fin d → ℝ)
      (negativeScale : ∀ {d : ℕ}, Fin d → ((Fin d → ℝ) → Fin d → ℝ) → ℝ)
      (sampleScale : ∀ {d : ℕ}, (Fin d → ℝ) → ℝ → ℝ)
      (directionScale : ∀ {d : ℕ}, ℝ → (Fin d → ℝ) → ℝ)
      (innerSampleProgram : ℕ → List RayInstruction)
      (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ),
      (∀ (d : ℕ) (i j : Fin d), axis i j = if j = i then 1 else 0) ∧
      (∀ (d : ℕ) (j : Fin d), negativeDirection d j = -1) ∧
      (∀ (d : ℕ) (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d),
        positiveScale oracle i = oracle (axis i) i) ∧
      (∀ (d : ℕ) (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ),
        negativeScale j oracle = -oracle (negativeDirection d) j) ∧
      (∀ (d : ℕ) (t : Fin d → ℝ) (s : ℝ),
        sampleScale t s = (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹) ∧
      (∀ (d : ℕ) (a : ℝ) (u : Fin d → ℝ),
        directionScale a u = a / (1 + ∑ i, |u i|)) ∧
      (∀ (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (horacle : IsPolytopeRayOracle P oracle)
        (u : Fin d → ℝ),
        let a := directionScale (sampleScale (positiveScale oracle) (negativeScale ⟨0, hd⟩ oracle)) u
        0 < a ∧ (-a) • u ∈ P ∧ a • u ∈ P) ∧
      (∀ (d : ℕ) (hd : 0 < d) (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        ∃ c : RayConfiguration,
          rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          c.pc = (d + 1) * (d + 2) + 2 ∧
          (innerSampleProgram d)[c.pc]? = some .halt ∧
          c.head = 0 ∧
          c.queries = q + (d + 1) ∧
          (∀ i : Fin (d + 1), ∀ j : Fin d,
            c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
          (∀ i : Fin d,
            c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) = positiveScale oracle i) ∧
          (-c.tape ((((d + 1) * d : ℕ) : ℤ)) = negativeScale ⟨0, hd⟩ oracle) ∧
          (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z)) := by sorry

end Grunbaum2003
