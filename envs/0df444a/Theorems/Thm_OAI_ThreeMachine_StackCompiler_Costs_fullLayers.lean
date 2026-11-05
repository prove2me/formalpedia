-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_fullLayers
-- name    : OAI.ThreeMachine.StackCompiler.Costs.fullLayers
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:34:57.108605+00:00
-- url     : https://prove2.me/theorems/ef89ccae-b23b-42ad-a194-a004cba01875
-- title:
--   Cost of all layers of the dynamic program
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. For $K\le 10000$, the routine `Uniform.fullLayers K`, computing `Algorithm.layers` over `effectiveFamily` with formula size $K$, has running time satisfying `Poly` of degree $150010$ in the number $n$ of jobs.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `SchedulingCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/SchedulingCosts.lean#L106

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem fullLayers (K : ℕ) (hk : K ≤ 10000) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.fullLayers K).time x.1 x.2) 150010 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
