-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_known_facet_step_eps_program
-- name    : Grunbaum2003.rayMachine_known_facet_step_eps_program
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:14:51.574225+00:00
-- url     : https://prove2.me/theorems/b3ebf994-a416-4fbf-b49c-8d3329659ec6
-- title:
--   Compiled straight-line ray-machine program for known-facet slack product, direction square sum, and safe perturbation step size
-- statement:
--   For any ambient dimension $d \ge 0$, any number $k \ge 0$ of learned facet rows stored on the tape at `rowBase + j * d + i`, any boundary point $p$ stored at `pBase + i`, any transverse direction $u$ stored at `uBase + i`, and any positive scale $a = \text{tape}(aCell) > 0$, there exists an explicit straight-line `List RayInstruction` program `stepEpsProgram d k rowBase pBase uBase aCell minBase` (depending only on the static parameters, never on the real input tape or oracle) that executes in `stepEpsSteps d k rowBase pBase uBase aCell` steps with zero oracle queries, never divides by zero whenever $\forall j < k,\; L_j(p) < 1$, writes the exact safe perturbation step size
--   $$
--   \varepsilon = \frac{a \cdot \delta}{2(1 + a \cdot M + \delta)}, \quad
--   \delta = \prod_{j=0}^{k-1} \frac{1 - L_j(p)}{1 + (1 - L_j(p))}, \quad
--   M = 1 + \sum_{j=0}^{k-1} (L_j(u))^2
--   $$
--   into `dst = stepEpsDest d k rowBase pBase uBase aCell minBase ≥ minBase`, and preserves all tape cells strictly below `dst`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem rayMachine_known_facet_step_eps_program :
  ∃ (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ),
    ∀ {d k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
      0 < source aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (pBase + (i.val : ℤ)) < 1) →
      let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let steps := stepEpsSteps d k rowBase pBase uBase aCell
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
        ∀ z : ℤ, z < dst → c'.tape z = source z := by sorry

end Grunbaum2003
