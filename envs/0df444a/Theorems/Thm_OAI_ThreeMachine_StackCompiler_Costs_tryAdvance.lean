-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_tryAdvance
-- name    : OAI.ThreeMachine.StackCompiler.Costs.tryAdvance
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:35:09.015081+00:00
-- url     : https://prove2.me/theorems/98abb31a-5e9b-46bb-ad3c-fcb32e02a617
-- title:
--   Cost of one table lookup and advance step
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let $J$ be an index type with $n:J\to\mathbb{N}$, suppose the lookup tables $\mathrm{tab}_j$ have length satisfying `Poly n` of degree $30000$ and contain only small blocks, and that the blocks in the marked states $u_j$ are small, where `BlockSmall b` means that the length of $b$ and all its time values are at most $n$. The routine `Uniform.tryAdvance`, which attempts `Algorithm.tryAdvance` from a marked state using the table, has running time satisfying `Poly n` of degree $60002$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `SolverCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/SolverCosts.lean#L77

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (v : ∀ j, Algorithm.State (Fin (n j)))

theorem tryAdvance
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryAdvance.time (n j) (U j,(tab j,(u j,v j)))) 60002 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
