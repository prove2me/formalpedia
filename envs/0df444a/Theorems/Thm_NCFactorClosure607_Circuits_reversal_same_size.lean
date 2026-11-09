-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_reversal_same_size
-- name    : NCFactorClosure607.Circuits.reversal_same_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:34.773946+00:00
-- url     : https://prove2.me/theorems/f80ae198-04c9-4133-a201-594cf9b4c8d2
-- title:
--   Reversal: swapping multiplication inputs gives a same-size circuit for $\mathrm{rev}(f)$
-- statement:
--   Let $\mathrm{rev}$ be the $F$-linear map on $F\langle X\rangle$ that reverses the order of letters in every word, so $\mathrm{rev}(PQ)=\mathrm{rev}(Q)\,\mathrm{rev}(P)$. Let $C$ be a circuit computing $f$, and let $C^{\mathrm{rev}}$ be obtained from $C$ by interchanging the two inputs of every multiplication gate. Then $C^{\mathrm{rev}}$ is a circuit with
--   $$C^{\mathrm{rev}}\text{ computes }\mathrm{rev}(f),\qquad \operatorname{size}(C^{\mathrm{rev}})=\operatorname{size}(C),\qquad \operatorname{synDeg}(C^{\mathrm{rev}})=\operatorname{synDeg}(C).$$
--
--   Reversal turns left-cofactor removal into right-cofactor removal, so one construction serves for left, right and central factors.
--
--   **Formalization Note** $\mathrm{rev}$ is Mathlib's `star` on `FreeAlgebra F X`, the algebra anti-automorphism fixing scalars and variables; it reverses every word.
--
--   Differences from the source:
--   - generalization: $X=\{x_1,\dots,x_m\}$ with $m\ge1$ → an arbitrary type `X`; reason: the statement for every type specializes to every finite nonempty variable set.
--   - generalization: same size and computes $\mathrm{rev}(f)$ → additionally the same syntactic degree; reason: the extra conclusion is used in the proof of Theorem 1.1 (p.10, the construction preserves syntactic degree), and the Lean statement implies the source's claim.
--   - encoding: $\mathrm{rev}$ (reverse words, extend linearly) → Mathlib `star` on `FreeAlgebra`; reason: `star` reverses every word and fixes scalars, so it is the same map.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.5, §2, paragraph Reversal; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Circuit

namespace NCFactorClosure607.Circuits

/-- §2, paragraph Reversal (p.5): interchanging the two inputs of every multiplication gate of
a circuit gives a circuit of the same size computing the reversed polynomial `rev f` (Mathlib's
`star` on `FreeAlgebra`, which reverses every word and fixes scalars); it also has the same
syntactic degree. -/
theorem reversal_same_size {F : Type*} [Field F] {X : Type*} (C : Circuit F X)
    (hC : C.WellFormed) :
    C.reverse.WellFormed ∧ C.reverse.eval = star C.eval ∧ C.reverse.size = C.size ∧
      C.reverse.synDeg = C.synDeg := by sorry

end NCFactorClosure607.Circuits
