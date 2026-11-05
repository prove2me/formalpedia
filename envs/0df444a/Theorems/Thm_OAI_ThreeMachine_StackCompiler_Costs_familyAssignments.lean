-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_familyAssignments
-- name    : OAI.ThreeMachine.StackCompiler.Costs.familyAssignments
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:34:54.168682+00:00
-- url     : https://prove2.me/theorems/e4059808-9e25-4c7f-bb84-6675d97106a6
-- title:
--   Cost of enumerating assignments of atoms to formula leaves
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. For $K\in\mathbb{N}$, the routine `Uniform.familyAssignments K` lists the functions from $K$ leaves to the atom sets. Its running time satisfies `Poly` of degree $\max(\max(100,9K+10),5)$ in the number $n$ of jobs, the exponent being linear in the fixed formula size $K$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `FamilyCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/FamilyCosts.lean#L190

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

universe u1

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (k : ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (xs : ∀ j, List (Finset (Fin (n j))))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable {K : ℕ} (r : ∀ j, Fin K → Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type}

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem familyAssignments (K : ℕ) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.familyAssignments K).time x.1 x.2) (max (max 100 (9*K+10)) 5) := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
