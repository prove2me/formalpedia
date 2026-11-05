-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_solveMarks
-- name    : OAI.ThreeMachine.StackCompiler.Costs.solveMarks
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:34:52.552558+00:00
-- url     : https://prove2.me/theorems/f7ac457d-8bca-4bc4-9276-f4dc977d9353
-- title:
--   Cost of computing the markings for one set
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let $J$ be an index type with $n:J\to\mathbb{N}$, with table lengths and family lengths satisfying `Poly n` of degree $30000$, candidate-triple list length of degree $3$, and with tables that are good for the precedence relation of $M_j$ and bounded: `Algorithm.TableGood` says that each stored block is a valid full schedule of its set, and `Algorithm.TableBounded` that each stored block has all time values at most its length. The routine `Uniform.solveMarks`, computing `Algorithm.markings` from `Algorithm.states`, has running time satisfying `Poly n` of degree $120009$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `MatrixCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/MatrixCosts.lean#L24

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

universe u1 u2 u3 u4 u5

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

theorem solveMarks
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.solveMarks.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120009 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
