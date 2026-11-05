-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_conePred
-- name    : OAI.ThreeMachine.StackCompiler.Costs.conePred
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:35:53.598308+00:00
-- url     : https://prove2.me/theorems/89d59b0e-1028-4cea-8162-b17a97823738
-- title:
--   Cost of computing a cone of a set of jobs
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. For a Boolean `frame`, the routine `Uniform.conePred frame` computes, from a set $Y$ of jobs, the set of vertices $v$ with a relation to some $y\in Y$, namely $y\prec v$ when `frame` is true and $v\prec y$ otherwise. Its running time satisfies `Poly` of degree $20$ in the number $n$ of jobs.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `RankCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/RankCosts.lean#L135

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

universe u1 u2

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.RankCellInput (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem conePred (frame : Bool) :
    Poly (fun x : Σ n, Universe n × (Matrix n × Finset (Fin n)) => x.1)
      (fun x => (Uniform.conePred frame).time x.1 x.2) 20 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
