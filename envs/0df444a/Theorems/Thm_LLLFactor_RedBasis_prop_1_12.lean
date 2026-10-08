-- Prove2me | Theorems.Thm_LLLFactor_RedBasis_prop_1_12
-- name    : LLLFactor.RedBasis.prop_1_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:19:59.628811+00:00
-- url     : https://prove2.me/theorems/8fc0ed95-f76a-4feb-983c-b0adb77f7b50
-- title:
--   (1.12) Proposition, p. 518 — |b_j|² ≤ 2^{n−1}·max|x_i|² for linearly independent x_1, …, x_t ∈ L
-- statement:
--   Let $L\subset\mathbb R^n$ ($n\ge1$) be a lattice with reduced basis $b_1,\ldots,b_n$, and let $x_1,\ldots,x_t\in L$ be linearly independent. Then
--
--   $$|b_j|^2\le 2^{n-1}\cdot\max\{|x_1|^2,|x_2|^2,\ldots,|x_t|^2\}\qquad\text{for }j=1,2,\ldots,t .$$
--
--   This is Proposition (1.12) of Lenstra–Lenstra–Lovász. Since independent vectors in $\mathbb R^n$ number at most $n$, it compares the first $t$ basis vectors with any $t$ independent lattice vectors; in particular each $|b_j|^2$ is within a factor $2^{n-1}$ of the $j$-th successive minimum of the lattice.
--
--   **Formalization Note** The maximum is `Finset.univ.sup'` over the index set $\{0,\ldots,t-1\}$, whose nonemptiness is witnessed by $j$ itself, so it is the true maximum with no default value. Lean indexes the basis by $\{0,\ldots,n-1\}$, so the paper's $b_i$ is Lean's `b ⟨i-1, _⟩`; a paper exponent $2^{i-1}$ at index $i$ becomes `2 ^ (i : ℕ)` at the Lean index. The guard $j<n$ only lets Lean form $b_j$; it holds automatically, since linear independence forces $t\le n$. The exponent $n-1$ is nontruncated because $n\ge1$. At $t=0$ the statement has no instance, exactly as the page's range $j=1,\ldots,t$ is empty.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 518, (1.12) Proposition; DOI: https://doi.org/10.1007/BF01457454

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.RedBasis

theorem prop_1_12 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Vec n))
  (b : Fin n → Vec n) (hb : IsBasisFor b L) (hred : IsReduced b)
  {t : ℕ} (x : Fin t → Vec n) (hxL : ∀ j, x j ∈ L)
  (hxind : LinearIndependent ℝ x) :
  ∀ j : Fin t, ∀ (hj : (j : ℕ) < n),
    ‖b ⟨j, hj⟩‖ ^ 2 ≤
      (2 : ℝ) ^ (n - 1) * Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ (fun i => ‖x i‖ ^ 2) := by sorry
end LLLFactor.RedBasis
