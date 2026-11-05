-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_unaryAnswer
-- name    : OAI.ThreeMachine.StackCompiler.Costs.unaryAnswer
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:35:09.424991+00:00
-- url     : https://prove2.me/theorems/7119c53e-8428-48b9-80e9-0df9147c9156
-- title:
--   Cost of computing the output from an instance
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let $J$ be an index type with $s,n:J\to\mathbb{N}$ where $n$ satisfies `Poly s` of degree $1$, let $G_j$ be instances on $n_j$ jobs with edge list length satisfying `Poly s` of degree $1$, and let $d_j$ be optional deadlines whose value (default $0$) satisfies `Poly s` of degree $1$. The routine `Uniform.unaryAnswer`, which first computes the reachability matrix and then the answer, has running time satisfying `Poly s` of degree $150011$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `RequestBounds.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/RequestBounds.lean#L27

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

theorem unaryAnswer (G : ∀ j, Instance (n j)) (d : J → Option ℕ)
    (hn : Poly s n 1) (he : Poly s (fun j => (G j).edges.length) 1)
    (hd : Poly s (fun j => (d j).getD 0) 1) :
    Poly s (fun j => Uniform.unaryAnswer.time (n j) (U j,(G j,d j))) 150011 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
