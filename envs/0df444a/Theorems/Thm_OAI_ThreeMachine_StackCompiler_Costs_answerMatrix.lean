-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_answerMatrix
-- name    : OAI.ThreeMachine.StackCompiler.Costs.answerMatrix
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:35:22.040193+00:00
-- url     : https://prove2.me/theorems/3f3e9009-5125-4c4e-b936-0999d51db609
-- title:
--   Cost of computing the output from a closed precedence matrix
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let $J$ be an index type with $s,n:J\to\mathbb{N}$ where $n$ satisfies `Poly s` of degree $1$, and let $d_j$ be optional deadlines whose value (default $0$) satisfies `Poly s` of degree $1$. The routine `Uniform.answerMatrix`, returning `answerMatrix M d`, namely a schedule for the deadline when $d$ is given and otherwise an optimal one, has running time satisfying `Poly s` of degree $150011$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `RequestBounds.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/RequestBounds.lean#L8

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))

theorem answerMatrix (d : J → Option ℕ) (hn : Poly s n 1)
    (hd : Poly s (fun j => (d j).getD 0) 1) :
    Poly s (fun j => Uniform.answerMatrix.time (n j) (U j,(M j,d j))) 150011 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
