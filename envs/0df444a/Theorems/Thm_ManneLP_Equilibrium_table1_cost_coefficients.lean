-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_table1_cost_coefficients
-- name    : ManneLP.Equilibrium.table1_cost_coefficients
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:45.853561+00:00
-- url     : https://prove2.me/theorems/f43f7085-63ff-4f61-b0b4-cf3a918b202b
-- title:
--   §6, Table 1 — the example's shortage costs (4, 2, 2, 0, 0, 0, 0) and cost coefficients cᵢⱼ = (4, 5, 3, 4, 2, 5, 3)
-- statement:
--   In the numerical example of §6 ($T=3$; $p_0=2/3$, $p_1=0$, $p_2=1/3$; $C_1(i)=i$, $C_2(j)=3j$, $C_3(m)=\max[0,6m]$; $j\in\{0,1\}$), the expected shortage costs $\sum_np_nC_3(n-i-j)$ on the pairs $(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0)$ are
--   $$
--   4,\ 2,\ 2,\ 0,\ 0,\ 0,\ 0,
--   $$
--   and the cost coefficients (10) $c_{ij}=C_1(i)+C_2(j)+\sum_np_nC_3(n-i-j)$ are
--   $$
--   c_{00}=4,\ c_{01}=5,\ c_{10}=3,\ c_{11}=4,\ c_{20}=2,\ c_{21}=5,\ c_{30}=3.
--   $$
--
--   These are the objective coefficients of the example's linear program.
--
--   **Formalization Note** The coefficients are computed from the general definition (10) applied to the example's data.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), p. 263 (PDF p. 6), §6, Table 1

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP
import Definitions.Def_ManneLP_Equilibrium_Example

namespace ManneLP.Equilibrium

theorem table1_cost_coefficients :
    (∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 0 - 0) = 4 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 0 - 1) = 2 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 1 - 0) = 2 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 1 - 1) = 0 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 2 - 0) = 0 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 2 - 1) = 0 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 3 - 0) = 0) ∧
    (costCoeff exampleModel 0 0 = 4 ∧ costCoeff exampleModel 0 1 = 5 ∧
      costCoeff exampleModel 1 0 = 3 ∧ costCoeff exampleModel 1 1 = 4 ∧
      costCoeff exampleModel 2 0 = 2 ∧ costCoeff exampleModel 2 1 = 5 ∧
      costCoeff exampleModel 3 0 = 3) := by sorry

end ManneLP.Equilibrium
