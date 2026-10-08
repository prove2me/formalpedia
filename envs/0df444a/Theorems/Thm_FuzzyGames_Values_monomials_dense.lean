-- Prove2me | Theorems.Thm_FuzzyGames_Values_monomials_dense
-- name    : FuzzyGames.Values.monomials_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:26.893208+00:00
-- url     : https://prove2.me/theorems/304df2b9-0609-48d0-b5ac-1a5153a700eb
-- title:
--   Theorem 8.1, proof — the monomials τ^k (k ≠ 0) span a dense subspace of V^n in the C¹ norm
-- statement:
--   Let $v\in V^n$ be a $C^1$ coalitional worth function vanishing at $0$ and let $\varepsilon>0$. Then there are finitely many nonzero exponents $k\in\mathbb N^n$ and real coefficients $a_k$ such that the polynomial $p(\tau)=\sum_k a_k\,\tau_1^{k_1}\cdots\tau_n^{k_n}$ satisfies
--   $$\sup_{\tau\in[0,1]^n}|v(\tau)-p(\tau)|+\sup_{\tau\in[0,1]^n}\|Dv(\tau)-Dp(\tau)\|<\varepsilon .$$
--
--   Hence a continuous linear map on $V^n$ is determined by its values on the monomials, which is how the uniqueness part of Theorem 8.1 is reduced to monomials.
--
--   **Formalization Note** The exponent $k=0$ is excluded because the constant $1$ does not vanish at $0$ and so is not in $V^n$. The seminorm is the $C^1$ seminorm of the cube, with the sup norm on $\mathbb R^n$; both suprema are finite because $v-p$ is $C^1$ and the cube is compact.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8, proof of Theorem 8.1, pp. 10–11

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

namespace FuzzyGames.Values

/-- §8, proof of Theorem 8.1 (pp. 10–11): the polynomials `τ ↦ τ_1^{k_1} ⋯ τ_n^{k_n}`
(`k ≠ 0`) span a dense subspace of `V^n` for the C¹ norm on the FuzzyGames.NTUCore.cube. -/
theorem monomials_dense (n : ℕ) (v : Vn n) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → ℝ), 0 ∉ K ∧
      c1seminorm (fun τ => v.1 τ - ∑ k ∈ K, a k * monomial k τ) < ε := by sorry

end FuzzyGames.Values
