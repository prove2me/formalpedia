-- Prove2me | Theorems.Thm_LindbladStructLearn_lemma_4_1
-- name    : LindbladStructLearn.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:00:50.451522+00:00
-- url     : https://prove2.me/theorems/96001dbc-fd69-445e-99bc-0bf610eb1fc6
-- title:
--   Lemma 4.1 — $\|J(x) - A\|_{B_1\to B_1} \le (23k)!\,gt$
-- statement:
--   Let $1 \le k \le n$, $g > 0$, let $x$ be a vector on the $k$-local pairs with $\|x\|_{B_1} \le g$, and let $0 < t < 1/(4ekg)$. Let $J(x)$ be the Jacobian of $y \mapsto E(y)/t$ at $x$ and $A = A_k$. Then for every vector $v$,
--
--   $$\big\|(J(x) - A)v\big\|_{B_1} \le (23k)!\,g\,t\,\|v\|_{B_1},$$
--
--   i.e. $\|J(x) - A\|_{B_1\to B_1} \le (23k)!\,gt$.
--
--   The lemma says that for short times the expectation values are well approximated by their linear term $tAx$, uniformly on the $B_1$ ball of radius $g$.
--
--   Differences from the source:
--   - encoding: the Jacobian J(x) of E(x)/t and the operator norm ‖J(x) − A‖_{B1→B1} → the complex Fréchet derivative of y ↦ E(y)/t applied to every vector v, ‖(J(x) − A)v‖_B1 ≤ (23k)!·g·t·‖v‖_B1; reason: E is holomorphic in x; the operator norm bound is the vector inequality for all v
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemma 4.1, Eq. (4.3), p.24

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_expVec
import Definitions.Def_LindbladStructLearn_Amat
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Lemma 4.1 (operator norm bound on higher-order terms; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (4.3), p.24): if
`‖x‖_B1 ≤ g` and `0 < t < 1/(4ekg)`, the Jacobian `J(x)` of `E(x)/t` satisfies
`‖J(x) − A‖_(B1→B1) ≤ (23k)! g t`, with `A = A_k` of Notation 3.2.

**Formalization Note** `J(x)` is the complex derivative (`fderiv ℂ`) of `y ↦ E(y)/t` on `ℂ^m`
(`m` the `k`-local pairs with `P₁ ≠ I`); the operator norm is stated vector by vector:
`‖(J(x) − A)v‖_B1 ≤ (23k)! g t ‖v‖_B1` for every `v`. `x` is any vector on the index set.
`k, g > 0` (standing assumption, p.13) and `k ≤ n` (the range of Notation 3.2). -/
theorem lemma_4_1 (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (g : ℝ) (hg : 0 < g)
    (x : Idx n k → ℂ) (hx : b1Norm (ext x) ≤ g) (t : ℝ) (ht : 0 < t)
    (ht' : t < 1 / (4 * Real.exp 1 * k * g)) (v : Idx n k → ℂ) :
    b1Norm (ext ((fderiv ℂ (fun y : Idx n k → ℂ => (1 / (t : ℂ)) • expVec t y) x) v -
        Matrix.mulVec (Amat n k) v)) ≤
      ((23 * k).factorial : ℝ) * g * t * b1Norm (ext v) := by sorry

end LindbladStructLearn
