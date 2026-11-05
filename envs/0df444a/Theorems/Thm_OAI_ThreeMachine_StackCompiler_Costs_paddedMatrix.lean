-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_paddedMatrix
-- name    : OAI.ThreeMachine.StackCompiler.Costs.paddedMatrix
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:34:53.146192+00:00
-- url     : https://prove2.me/theorems/2bb34987-4b3f-483b-9641-d1c665f229bc
-- title:
--   Cost of building the precedence matrix of the padded instance
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. The routine `Uniform.paddedMatrix` takes a precedence matrix on $i_1$ jobs and a universe on $i_2$ points, and produces the Boolean matrix of `paddedOrder`, the same order extended by isolated jobs. Its running time satisfies `Poly` of degree $1000$ in $i_1+i_2$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `MatrixCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/MatrixCosts.lean#L220

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

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u5} (s n : J → ℕ) (M : ∀ j, Matrix (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

theorem paddedMatrix : Poly (fun x : Σ i : ℕ × ℕ, Universe i.2 × Matrix i.1 => x.1.1+x.1.2)
    (fun x => Uniform.paddedMatrix.time x.1 x.2) 1000 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
