-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_scDEFHIJ
-- name    : OAI.ThreeMachine.StackCompiler.Costs.scDEFHIJ
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:34:53.512197+00:00
-- url     : https://prove2.me/theorems/43ebb3ed-e99e-4b32-bf9c-f7599eb19634
-- title:
--   Cost of the conjunction of the last state-compatibility checks
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Here `Uniform.scDEFHIJ` is the routine evaluating, on an input consisting of a universe, a matrix, a state and a set, the last clauses of `Algorithm.State.Compatible`: the middle and right parts are disjoint, the middle has three elements, and the relation has no edges from middle to middle, middle to left, right to left, and right to middle. Its running time satisfies `Poly` of degree $5$ in the number $n$ of jobs.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `StateCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/StateCosts.lean#L174

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u7} {α : I → Type u8} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
namespace Costs

end Costs
namespace Uniform

end Uniform
namespace Costs

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

theorem scDEFHIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scDEFHIJ.time x.1 x.2) 5 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
