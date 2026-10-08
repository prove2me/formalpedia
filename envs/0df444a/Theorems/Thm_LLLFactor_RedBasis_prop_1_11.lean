-- Prove2me | Theorems.Thm_LLLFactor_RedBasis_prop_1_11
-- name    : LLLFactor.RedBasis.prop_1_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:19:43.42588+00:00
-- url     : https://prove2.me/theorems/e245ab65-4eef-4829-af15-7c19b3ab5163
-- title:
--   (1.11): first reduced-basis vector versus any lattice vector
-- statement:
--   Let $L\subset\mathbb R^n$ ($n\ge1$) be a lattice with reduced basis $b_1,\ldots,b_n$. Then
--
--   $$|b_1|^2\le 2^{n-1}\,|x|^2\qquad\text{for every }x\in L,\ x\ne0 .$$
--
--   This is Proposition (1.11): the first vector of a reduced basis is within a factor $2^{(n-1)/2}$ of the shortest nonzero vector of the lattice. It is what makes reduced bases useful for approximating shortest vectors, and it is the case $t=1$ of Proposition (1.12).
--
--   **Formalization Note** $b_1$ is Lean's `b ⟨0, hn⟩`; the exponent $n-1$ is a natural-number subtraction, nontruncated because $n\ge1$.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 518, (1.11) Proposition; DOI: https://doi.org/10.1007/BF01457454

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.RedBasis

theorem prop_1_11 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Vec n))
  (b : Fin n → Vec n) (hb : IsBasisFor b L) (hred : IsReduced b)
  (x : Vec n) (hxL : x ∈ L) (hx0 : x ≠ 0) :
  ‖b ⟨0, hn⟩‖ ^ 2 ≤ (2 : ℝ) ^ (n - 1) * ‖x‖ ^ 2 := by sorry
end LLLFactor.RedBasis
