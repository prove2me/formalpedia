-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_requestRawBound_length
-- name    : OAI.ThreeMachine.StackCompiler.requestRawBound_length
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:33:45.393937+00:00
-- url     : https://prove2.me/theorems/ff22684c-339c-47cf-9c5b-a2daeed6d8bd
-- title:
--   Raw machine bound for deadlines not exceeding the job count
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let `SmallDeadline` be the type of requests whose deadline is either absent or at most the number of jobs. For $x$ in this type, let $L$ be the length of the bit encoding `RequestData.bits` of the request. Then the raw time bound for the compiled machine, `requestRawBound x` $=2000\,(\mathrm{time}+L+|\mathrm{out}|+1)$, with `time` the running time of `Uniform.requestAnswer` on the request and `out` the bit list `Algorithm.output` of the request, satisfies `Poly` of degree $150020$ in $L$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `Main.lean` (openai/math, Apache-2.0, credit OpenAI). It is derived from `requestRawBound_poly` and gives the running-time bound used in `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/Main.lean#L46

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

section
namespace ThreeMachine.StackCompiler

theorem requestRawBound_length : Poly (fun x : SmallDeadline => (RequestData.bits x.1).length)
    (fun x => requestRawBound x.1) 150020 := by
  sorry

end ThreeMachine.StackCompiler
end
end OAI
