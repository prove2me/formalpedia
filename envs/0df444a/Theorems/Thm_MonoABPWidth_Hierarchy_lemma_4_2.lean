-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_2
-- name    : MonoABPWidth.Hierarchy.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T08:15:15.223848+00:00
-- url     : https://prove2.me/theorems/6bc9644f-a7d3-4fae-9aba-64da2c1512a4
-- title:
--   Lemma 4.2 — closure of a monomial rectangle
-- statement:
--   Let $k,n\ge1$ and let $f_1,f_2,g_1,g_2$ be monomials in the variables of $\operatorname{imm}_{k,n}$, including the unit monomial. Then
--   $$
--   f_1g_1,f_1g_2,f_2g_2\in\operatorname{supp}(\operatorname{imm}_{k,n})
--   \quad\Longrightarrow\quad f_2g_1\in\operatorname{supp}(\operatorname{imm}_{k,n}).
--   $$
--   This is the rectangle-closure property used in width-two completion. Monomials are exponent vectors, and their multiplication is addition of those vectors; coefficients are absent from the assertion.
--
--   Differences from the source:
--   - reading: matrix-chain length n ∈ ℕ, without an empty-chain convention → n ≥ 1 (and m ≥ 1 for divisors); reason: the paper specifies n matrices and k^(n−1) monomials (pp.4,10); an empty product and a depth-zero program would falsify the goal
--   - encoding: the (1,1) entry of a k-by-k matrix product → k ≥ 1; reason: the source entry is defined only in positive matrix dimension; no defined instance is excluded
--   - encoding: monomial multiplication with one-based matrix entries → addition of finitely supported natural exponent vectors with zero-based entries; reason: the zero exponent vector represents the unit; the representation preserves every monomial and product
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma 4.2, p. 7, PDF 8

import Definitions.Def_SetMultCost_imm

namespace MonoABPWidth.Hierarchy

/-- Lemma 4.2, p.7 / PDF8. Monomials are exponent vectors; vector addition
is monomial multiplication and the zero vector is the unit monomial. -/
theorem lemma_4_2 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (f₁ f₂ g₁ g₂ : SetMultCost.IMMVar k n →₀ ℕ)
    (h11 : f₁ + g₁ ∈ (SetMultCost.imm ℝ k n).support)
    (h12 : f₁ + g₂ ∈ (SetMultCost.imm ℝ k n).support)
    (h22 : f₂ + g₂ ∈ (SetMultCost.imm ℝ k n).support) :
    f₂ + g₁ ∈ (SetMultCost.imm ℝ k n).support := by sorry

end MonoABPWidth.Hierarchy
