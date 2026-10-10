-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedNestedEndpointDimension_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedNestedEndpointDimension_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T07:49:49.939859+00:00
-- url     : https://prove2.me/theorems/c658223e-839c-4225-967c-cc5e6033c2a1
-- title:
--   The comparison dimension and nX + mM lie below the nested forward parameter
-- statement:
--   Let $s, m \in \mathbb N$ with $m \le s$; $A \in \mathbb N$ and $\mathrm{constants} : \mathbb N \to \mathbb N$; $\mathrm{innerDepth}, \mathrm{outer}, \mathrm{inner} \in \mathbb N$; and reals $B_{\mathrm{struct}}$ and $p_{\mathrm{num}}$. Assume `preparedNestedEndpointDimensionExponent s` $\le A$ (the exponent is a natural number chosen by OpenAI's existence lemma for a uniform endpoint-dimension budget), $1 \le \mathrm{outer}$, $0 \le B_{\mathrm{struct}}$, and $p_{\mathrm{num}} \in [0, B_{\mathrm{struct}}]$; and let $n_X, M \in \mathbb N$ with $n_X \le B_{\mathrm{struct}}$ and $M \le B_{\mathrm{struct}}$. Write $F =$ `preparedFiniteForwardParameter A constants inner` $\bigl(\texttt{candidateNestedForwardSeed A constants innerDepth outer}\ B_{\mathrm{struct}}\bigr)$, where both functions are evaluations of polynomials with natural-number coefficients determined by their natural-number arguments. Then
--   $$\texttt{allocatedComparisonDimension}\ m\ p_{\mathrm{num}} \le F \quad\text{and}\quad n_X + mM \le F,$$
--   where `allocatedComparisonDimension m p` $= (m+1) + p + ((m+1)(p+1)^{m+1} + 1) + 2^{m+1} + (m+2)p + 2mp + 2mp\cdot 2^{m+1} + $ `comparisonProfileBound`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedNestedEndpointDimension_bounds` in `lean/OAI/Combinatorics/Progressions/Dynamics/PreparedNestedEndpointDimensionBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B185` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/PreparedNestedEndpointDimensionBudget.lean#L61

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B185

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedNestedEndpointDimension_bounds
    (s m : ℕ) (hm : m ≤ s) (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer inner : ℕ) {Bstruct pnum : ℝ}
    (hA : preparedNestedEndpointDimensionExponent s ≤ A)
    (houter : 1 ≤ outer) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (nX M : ℕ) (hnX : (nX : ℝ) ≤ Bstruct) (hM : (M : ℝ) ≤ Bstruct) :
    allocatedComparisonDimension m pnum ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) ∧
    ((nX + m * M : ℕ) : ℝ) ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
