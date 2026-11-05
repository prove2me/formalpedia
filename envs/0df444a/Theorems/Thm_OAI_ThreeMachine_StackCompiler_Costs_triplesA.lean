-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_triplesA
-- name    : OAI.ThreeMachine.StackCompiler.Costs.triplesA
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:35:22.366958+00:00
-- url     : https://prove2.me/theorems/3552b42e-3213-4277-ac35-64d73820d132
-- title:
--   Cost of converting all ordered triples to sets
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. The routine `Uniform.triplesA` lists all ordered triples of the $n$ points (`Uniform.triplesE`) and maps each to the set of its entries. Its running time satisfies `Poly` of degree $20$ in $n$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `RankCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/RankCosts.lean#L149

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

theorem triplesA : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.triplesA.time x.1 x.2) 20 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
