-- Prove2me | Theorems.Thm_OAI_HadamardSix_fourth_power_sum_zero
-- name    : OAI.HadamardSix.fourth_power_sum_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:17:35.802619+00:00
-- url     : https://prove2.me/theorems/f7430691-2f1e-40e9-9296-242efba5611c
-- title:
--   Six unimodular numbers with vanishing first and second power sums have vanishing fourth power sum
-- statement:
--   Let $v_0,v_1,\dots,v_5$ be six complex numbers of modulus one, that is $|v_i|=1$ for $i=0,\dots,5$. Suppose that their first and second power sums vanish,
--   $$\sum_{i=0}^{5} v_i=0\qquad\text{and}\qquad\sum_{i=0}^{5} v_i^{2}=0 .$$
--   Then their fourth power sum vanishes as well:
--   $$\sum_{i=0}^{5} v_i^{4}=0 .$$
--
--   The modulus-one hypothesis cannot be dropped: the six roots of $X^{6}+X^{2}$ (namely $0$ twice and the four primitive eighth roots of unity) have vanishing first and second power sums, but their fourth power sum is $-4$.
--
--   These hypotheses hold for the row ratios $r_k=H_{ik}\overline{H_{jk}}$ of two distinct rows of a $6\times 6$ complex Hadamard matrix $H$ whose entrywise square is also complex Hadamard: the ratios are unimodular because the entries of $H$ are, and their first and second power sums vanish by orthogonality of the rows of $H$ and of its entrywise square. The extra relation $\sum_k r_k^{4}=0$ is the input needed to show that these ratios sum to zero over each cube fibre $\{k: r_k^{3}=a\}$ when the cubes $r_k^{3}$ take only two values.
--
--   **Formalization Note** The six numbers are a function `v : Index → ℂ` with `Index = Fin 6`, and the modulus is the complex norm `‖v i‖`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/Hadamard/Polynomials.lean#L193-L209

import Mathlib
import Definitions.Def_HadamardCubeFiber
import Definitions.Def_OAI_LinearAlgebra_Hadamard_Polynomials

open OAI OAI.HadamardSix
open scoped BigOperators Matrix

theorem OAI.HadamardSix.fourth_power_sum_zero (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) : ∑ i, v i ^ 4 = 0 := by sorry
