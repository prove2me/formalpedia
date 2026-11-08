-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_vector_eval_and_perturbed_ray_query_program
-- name    : Grunbaum2003.rayMachine_vector_eval_and_perturbed_ray_query_program
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:33:54.243181+00:00
-- url     : https://prove2.me/theorems/ab466c3f-8cfe-47c5-bc0d-cc7b7ed1256e
-- title:
--   Compiled multi-coordinate vector evaluator and in-place perturbed ray-oracle query program
-- statement:
--   For any ambient dimension $d \ge 0$, any point $p$ stored at `pBase .. pBase + (d - 1)`, any transverse direction $u$ stored at `uBase .. uBase + (d - 1)`, and any perturbation step size $\varepsilon$ stored at `epsCell`, there exists an explicit straight-line ray-machine program `perturbedRayQueryProgram d pBase uBase epsCell minBase` that evaluates the $d$ coordinates $p_i + \varepsilon u_i$ into a fresh output block `outBase .. outBase + (d - 1)` (`outBase ≥ minBase`), shifts the head to `outBase`, executes `.query` in place (using 1 oracle query), shifts the head back to `0`, and halts with $\operatorname{oracle}(p + \varepsilon u)$ stored at `outBase .. outBase + (d - 1)` while preserving all tape cells strictly below `outBase`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun

set_option autoImplicit false

namespace Grunbaum2003

theorem rayMachine_vector_eval_and_perturbed_ray_query_program :
  ∃ (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ),
    ∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase uBase epsCell minBase : ℤ) (q : ℕ),
      (fun i : Fin d =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      let steps := perturbedRayQuerySteps d pBase uBase epsCell
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q + 1 ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z) := by sorry

end Grunbaum2003
