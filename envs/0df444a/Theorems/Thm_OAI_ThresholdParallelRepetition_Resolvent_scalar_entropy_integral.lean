-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_Resolvent_scalar_entropy_integral
-- name    : OAI.ThresholdParallelRepetition.Resolvent.scalar_entropy_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:40:23.857717+00:00
-- url     : https://prove2.me/theorems/0425378a-ddb1-4af7-839a-12b357d18c6e
-- title:
--   Integral representation of $t\log t$ for $0\le t\le1$
-- statement:
--   Let $t$ be a real number with $0\le t\le1$. Then the function
--   $$
--   s\longmapsto\frac{t}{1+s}-\frac{t}{t+s}
--   $$
--   is Lebesgue integrable on the half-line $(0,\infty)$, and
--   $$
--   \int_0^\infty\Big(\frac{t}{1+s}-\frac{t}{t+s}\Big)\,ds=t\log t .
--   $$
--   For $t=0$ the integrand vanishes identically and both sides are $0$.
--
--   Applied eigenvalue by eigenvalue through the functional calculus, this identity represents $A\log A$, for a Hermitian matrix $A$ with $0\preceq A\preceq I$, as the integral over $s\in(0,\infty)$ of $\frac{1}{1+s}A-A(A+sI)^{-1}$. That integral representation is the starting point of the operator entropy estimates that compare an average of effects with the individual effects.
--
--   **Formalization Note** The statement is the conjunction of `IntegrableOn (fun s => t / (1 + s) - t / (t + s)) (Ioi 0)` and the equality of the set integral over `Ioi 0` with `t * Real.log t`. Lean's conventions $\log0=0$ and $x/0=0$ play no role: for $t>0$ no denominator vanishes on $(0,\infty)$, and at $t=0$ both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Resolvent.lean#L189-L234

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.Resolvent
universe u_n u_J
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology

theorem OAI.ThresholdParallelRepetition.Resolvent.scalar_entropy_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntegrableOn (fun s : ℝ => t / (1 + s) - t / (t + s)) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, t / (1 + s) - t / (t + s)) = t * Real.log t := by sorry
