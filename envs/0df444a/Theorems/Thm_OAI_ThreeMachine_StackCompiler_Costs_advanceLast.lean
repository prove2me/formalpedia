-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_advanceLast
-- name    : OAI.ThreeMachine.StackCompiler.Costs.advanceLast
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:34:55.813827+00:00
-- url     : https://prove2.me/theorems/6e51535a-6a87-4a75-96f9-a91d0c06e4e7
-- title:
--   Cost of the final state advance for small blocks
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let $J$ be an index type with $n:J\to\mathbb{N}$, and suppose that the blocks $c_j$ and the block component of the states $u_j$ are small, where `BlockSmall b` means that the length of $b$ and all its time values are at most $n$. The routine `Uniform.advanceLast`, computing the state advance on these inputs, has running time satisfying `Poly n` of degree $7$.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `TransitionCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/TransitionCosts.lean#L312

import Mathlib
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.BlockAppendCellInput (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (W : ∀ j, Finset (Fin (n j)))
variable (b c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (v : ∀ j, Algorithm.State (Fin (n j))) (b c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u5} {α : I → Type u6} {β : I → Type u7} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (c : ∀ j, Algorithm.Block (Fin (n j)))

theorem advanceLast (hb : ∀ j, BlockSmall (u j).2) (hc : ∀ j, BlockSmall (c j)) :
    Poly n (fun j => Uniform.advanceLast.time (n j) (c j,(U j,u j))) 7 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
