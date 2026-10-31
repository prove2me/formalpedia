-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_remark_3_1_counterexample
-- name    : KallMayerSLP.KKT.remark_3_1_counterexample
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:12.145434+00:00
-- url     : https://prove2.me/theorems/90a0a8dd-c273-4628-918e-699df64849ba
-- title:
--   Remark 3.1 — RC 0 fails for $\min\{x\in\mathbb R^1\mid x^2\le 0\}$
-- statement:
--   Consider the one-dimensional program
--   $$
--   \min\{x\in\mathbb R^1\mid x^2\le 0\},
--   $$
--   i.e. $n=m=1$, $f(x)=x$, $g_1(x)=x^2$. Then
--
--   1. the feasible set is $\mathcal B=\{0\}$,
--   2. $\hat x=0$ is an optimal solution, and
--   3. the regularity condition RC 0 does not hold.
--
--   This shows that RC 0 can fail for nonlinear (even convex, smooth) constraints, which is why a regularity assumption such as Slater's condition is needed in Proposition 3.4.
--
--   Differences from the source:
--   - encoding: ℝ¹ → EuclideanSpace ℝ (Fin 1), coordinate x 0; reason: Lean convention; the same space
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, Remark 3.1, p.63 (PDF 74)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_RC0

namespace KallMayerSLP.KKT

/-- **Remark 3.1 (second part): `RC 0` fails for `min{x ∈ ℝ¹ | x² ≤ 0}`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, Remark 3.1, p.63 (PDF 74): "In the nonlinear case it may happen that the above regularity
condition does not hold. Take for example the elementary problem `min{x ∈ ℝ¹ | x² ≤ 0}`. Since
there is only one feasible solution, `x̂ = 0`, this is simultaneously the optimal solution of the
problem. Here `zᵀ∇gᵢ(x̂) ≤ 0` means that `2 · z · x̂ ≤ 0`, which is true for all `z ∈ ℝ¹` since
`x̂ = 0`, but `zᵀ∇f(x̂) = z · 1 < 0 ∀z < 0`, such that `RC 0` is violated."

The program has `n = m = 1`, objective `f(x) = x` and one constraint `g₁(x) = x² ≤ 0`; the
statement has three conjuncts: the feasible set is `{0}`, `0` is optimal, and `RC 0` fails.

**Formalization Note.** `ℝ¹` is `EuclideanSpace ℝ (Fin 1)`, a point `x` has the single coordinate
`x 0`. -/
theorem remark_3_1_counterexample :
    feasibleSet (fun (_ : Fin 1) (x : EuclideanSpace ℝ (Fin 1)) => x 0 ^ 2) = {0} ∧
    IsOptimal (fun x : EuclideanSpace ℝ (Fin 1) => x 0)
      (fun (_ : Fin 1) (x : EuclideanSpace ℝ (Fin 1)) => x 0 ^ 2) 0 ∧
    ¬ RC0 (fun x : EuclideanSpace ℝ (Fin 1) => x 0)
      (fun (_ : Fin 1) (x : EuclideanSpace ℝ (Fin 1)) => x 0 ^ 2) := by sorry

end KallMayerSLP.KKT
