-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_layerStep
-- name    : OAI.ThreeMachine.StackCompiler.Costs.layerStep
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:35:07.884708+00:00
-- url     : https://prove2.me/theorems/1736b118-a2b0-4d0c-b519-69e9b5e5781c
-- title:
--   Cost of one layer of the dynamic program
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let $J$ be an index type with $n:J\to\mathbb{N}$, with table and family lengths satisfying `Poly n` of degree $30000$, candidate-triple list length of degree $3$, and tables good for $M_j$ and bounded: `Algorithm.TableGood` says that each stored block is a valid full schedule of its set, and `Algorithm.TableBounded` that each stored block has all time values at most its length. The routine `Uniform.layerStep`, which solves the given family of sets from the table (`Algorithm.solve`) and records the results (`Algorithm.tableOf`), has running time satisfying `Poly n` of degree $150009$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `SchedulingCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/SchedulingCosts.lean#L9

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

theorem layerStep
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.layerStep.time (n j) ((U j,(M j,(fs j,zs j))),tab j)) 150009 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
