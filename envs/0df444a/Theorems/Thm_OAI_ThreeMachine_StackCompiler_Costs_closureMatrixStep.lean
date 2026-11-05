-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_closureMatrixStep
-- name    : OAI.ThreeMachine.StackCompiler.Costs.closureMatrixStep
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:33:57.014496+00:00
-- url     : https://prove2.me/theorems/6b06ed79-7378-48e3-991d-fe2372395f59
-- title:
--   Cost of one transitive-closure iteration
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. The routine `Uniform.closureMatrixStep` carries a universe and a matrix $M$ and replaces the current matrix $R$ by `nextMatrix M R`. Its running time satisfies `Poly` of degree $20$ in the number $n$ of jobs.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `OutputCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/OutputCosts.lean#L113

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

universe u1 u2 u3

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler

end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

namespace Poly
variable {J : Type} {s n : J → ℕ} {d e : ℕ}

end Poly
namespace Costs

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs

theorem closureMatrixStep : Poly
    (fun x : Σ n, (Universe n × Matrix n) × Matrix n => x.1)
    (fun x => Uniform.closureMatrixStep.time x.1 x.2) 20 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
