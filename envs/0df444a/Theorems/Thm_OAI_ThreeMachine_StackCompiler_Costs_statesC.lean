-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_statesC
-- name    : OAI.ThreeMachine.StackCompiler.Costs.statesC
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:33:21.142865+00:00
-- url     : https://prove2.me/theorems/b434eb11-fad5-4429-a5b5-f3e5c129d1bf
-- title:
--   Cost of forming one candidate state
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. The routine `Uniform.statesC` takes a pair of sets $(Y,Z)$, a universe and a set $W$ of jobs on $n$ points and returns the candidate state `Algorithm.State.candidate W Y Z`. Its running time satisfies `Poly` of degree $5$ in $n$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `TransitionCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/TransitionCosts.lean#L28

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

theorem statesC : Poly (fun x : Σ n, (Finset (Fin n) × Finset (Fin n)) ×
    (Universe n × Finset (Fin n)) => x.1)
    (fun x => Uniform.statesC.time x.1 x.2) 5 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
