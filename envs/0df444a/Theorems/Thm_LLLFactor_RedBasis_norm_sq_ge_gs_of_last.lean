-- Prove2me | Theorems.Thm_LLLFactor_RedBasis_norm_sq_ge_gs_of_last
-- name    : LLLFactor.RedBasis.norm_sq_ge_gs_of_last
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:19:34.303948+00:00
-- url     : https://prove2.me/theorems/bdbda481-37be-4fc5-b1b3-2acadf7ae25f
-- title:
--   Proof of (1.11) and (1.13): last nonzero coordinate
-- statement:
--   Let $b_1,\ldots,b_n$ be linearly independent vectors in $\mathbb R^n$ ($n\ge1$) with Gram–Schmidt vectors $b_i^*$, and let $x=\sum_{l=1}^n r_lb_l$ with integers $r_l$. If $i$ is the largest index with $r_i\neq0$, then
--
--   $$|x|^2\ \ge\ |b_i^*|^2 .$$
--
--   Indeed, writing $x=\sum_l r_l'b_l^*$, the coefficient $r_i'$ equals the integer $r_i\ne0$, so $|x|^2\ge r_i'^2|b_i^*|^2\ge|b_i^*|^2$. This is the step of the proof of Proposition (1.11) that the proof of (1.12) reuses as (1.13): a nonzero lattice vector is at least as long as the Gram–Schmidt vector at its last nonzero coordinate.
--
--   **Formalization Note** "$i$ is the largest index with $r_i\ne0$" is stated as $r_i\ne0$ and $r_l=0$ for every $l>i$. Lean indexes the basis by $\{0,\ldots,n-1\}$, so the paper's $b_i$ is Lean's `b ⟨i-1, _⟩`; a paper exponent $2^{i-1}$ at index $i$ becomes `2 ^ (i : ℕ)` at the Lean index. Reducedness is not used by this step and is not assumed.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 518, proof of (1.11), reused at (1.13); DOI: https://doi.org/10.1007/BF01457454

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.RedBasis

theorem norm_sq_ge_gs_of_last {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n)
  (hb : LinearIndependent ℝ b) (r : Fin n → ℤ) (i : Fin n)
  (hri : r i ≠ 0) (hlast : ∀ l, i < l → r l = 0) :
  ‖gs b i‖ ^ 2 ≤ ‖∑ l : Fin n, ((r l : ℤ) : ℝ) • b l‖ ^ 2 := by sorry
end LLLFactor.RedBasis
