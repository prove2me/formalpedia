-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_footnote5_implicit_prices
-- name    : ManneLP.Equilibrium.footnote5_implicit_prices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:14:11.122787+00:00
-- url     : https://prove2.me/theorems/bf1ee08b-4b9f-4686-bb1f-876bb13b9143
-- title:
--   Footnote 5 — the implicit prices −7/3, −13/3, −11/3 on (8.1)–(8.3), with 31/9 on (4), are an optimal dual solution
-- statement:
--   In the numerical example of §6, write the constraints as in Table 2: (4) $\sum_{i,j}x_{ij}=1$ and, for $t=1,2,3$, the row (8.t) "left-hand side minus right-hand side",
--   $$
--   a_{t,ij}=[\,i=t\,]-\sum_{n:\ i+j-n=t}p_n ,\qquad \sum_{i,j}a_{t,ij}x_{ij}=0 .
--   $$
--   Attach the price $u=31/9$ to (4) and the implicit prices
--   $$
--   v_1=-\tfrac73,\qquad v_2=-\tfrac{13}3,\qquad v_3=-\tfrac{11}3
--   $$
--   to (8.1)–(8.3). Then
--
--   1. (dual feasibility) $u+\sum_{t=1}^3v_ta_{t,ij}\le c_{ij}$ for every admissible pair $(i,j)$;
--   2. (tight columns) equality holds for $(0,1)$, $(1,1)$, $(2,0)$ and $(3,0)$, the columns of the basis of Table 2;
--   3. (equal objectives) the dual objective $u$ equals the objective value of the optimal solution $x^*$ of Table 2.
--
--   Hence $(u,v_1,v_2,v_3)$ is an optimal solution of the dual linear program. The prices measure, in Manne's words, "the comparative advantage of beginning the Markov process with an inventory level of 1, 2, or 3 units".
--
--   **Formalization Note** The page prints the prices of (8.1)–(8.3) only; the price $31/9$ of (4) is not printed and is the one forced by equality of the primal and dual objectives. The rows are signed as in Table 2. The dual optimum is not unique (the primal optimum is degenerate), and uniqueness is not claimed. The coefficient $a_{t,ij}$ is obtained by applying the general row (8.t) to the unit vector of the pair $(i,j)$.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), p. 265 (PDF p. 8), footnote 5 (to §7 (4), pp. 264–265); rows from Table 2, p. 263

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP
import Definitions.Def_ManneLP_Equilibrium_Example

namespace ManneLP.Equilibrium

theorem footnote5_implicit_prices :
    let u : ℝ := 31 / 9
    let v : ℕ → ℝ := fun t =>
      if t = 1 then -7 / 3 else if t = 2 then -13 / 3 else if t = 3 then -11 / 3 else 0
    let e : ℕ × ℕ → ℕ × ℕ → ℝ := fun a b => if b = a then 1 else 0
    let reduced : ℕ × ℕ → ℝ := fun a =>
      u + ∑ t ∈ Finset.Icc 1 3,
        v t * (marginal exampleModel (e a) t - rhsPos exampleModel (e a) t)
    (∀ a ∈ exampleModel.A, reduced a ≤ costCoeff exampleModel a.1 a.2) ∧
    (∀ a ∈ ({(0, 1), (1, 1), (2, 0), (3, 0)} : Finset (ℕ × ℕ)),
      reduced a = costCoeff exampleModel a.1 a.2) ∧
    u = lpObj exampleModel exampleOptimal := by sorry

end ManneLP.Equilibrium
