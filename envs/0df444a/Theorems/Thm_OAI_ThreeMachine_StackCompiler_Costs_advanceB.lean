-- Prove2me | Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_advanceB
-- name    : OAI.ThreeMachine.StackCompiler.Costs.advanceB
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T06:33:32.743798+00:00
-- url     : https://prove2.me/theorems/d962b6e6-1515-49af-9dce-96a9a4e864fb
-- title:
--   Cost of appending a selected triple to a block
-- statement:
--   Throughout, a *routine* `R : Uniform f` is a program in the compiler's while-language `Code`, with a charge function, that computes the function family $f_i$ on encoded data. `R.time i x` is the charge of $R$ on the encoding of $x$, a natural number that bounds the number of evaluation steps of the program on that input. For $s,f:I\to\mathbb{N}$, the predicate `Poly s f d` means that there is a constant $C$ with $f(i)\le C\,(s(i)+2)^d$ for all $i\in I$. Let $J$ be an index type with $n:J\to\mathbb{N}$, and let $b_j,c_j$ be blocks whose volumes, the sizes of their encodings (`volume`), satisfy `Poly n` of degree $2$. On an input $(U_j,(v_j,(b_j,c_j)))$, the routine `Uniform.advanceB` returns `Block.append v.left b Block.triple`: the block $b$ followed by one new slot, where jobs in the left part of the state $v_j$ keep their times from $b$ and all other jobs get the new slot. The block $c_j$ does not affect this output. The running time satisfies `Poly n` of degree $5$ on these inputs.
--
--   **Formalization Note** The statement is reproduced verbatim from upstream `TransitionCosts.lean` (openai/math, Apache-2.0, credit OpenAI). It feeds the bound `requestRawBound_poly` and the running-time statement of `main_theorem`.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math, cost bounds of the stack compiler. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/TransitionCosts.lean#L186

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

theorem advanceB (hb : Poly n (fun j => volume (b j)) 2)
    (hc : Poly n (fun j => volume (c j)) 2) :
    Poly n (fun j => Uniform.advanceB.time (n j) (U j,(v j,(b j,c j)))) 5 := by
  sorry

end ThreeMachine.StackCompiler.Costs
end
end OAI
