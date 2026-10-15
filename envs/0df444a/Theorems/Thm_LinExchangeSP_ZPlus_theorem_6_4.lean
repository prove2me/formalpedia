-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_theorem_6_4
-- name    : LinExchangeSP.ZPlus.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:40.933296+00:00
-- url     : https://prove2.me/theorems/de6a1baa-e1bb-438b-a29a-d84c479b8f85
-- title:
--   Theorem 6.4, p. 15 — a Z₊-matrix polyhedron P_M lies between an M2VPI polyhedron with at most ℓ rows and B²·P_M
-- statement:
--   Let $M \in \mathcal{Z}_+(k,t)$ be a $Z_+$-matrix (off-diagonal entries nonpositive, column sums nonnegative) with $k \ge 1$ rows and $\ell$ nonzero entries, and let $b \in \mathbb{Q}^k$ with $b > 0$. Let
--
--   $$P_M = \{x \in \mathbb{R}^t : Mx \le b,\ x \ge 0\},\qquad B = \frac{\sum_{j=1}^k b_j}{\min_{i\in[k]} b_i}.$$
--
--   Then there exist $\ell' \le \ell$, a rational matrix $\bar M \in \mathcal{M}_2(\ell',t)$ (at most one positive and at most one negative entry per row) and $\bar b \in \mathbb{Q}^{\ell'}$ such that
--
--   $$P_M \subseteq \{x \in \mathbb{R}^t : \bar Mx \le \bar b,\ x \ge 0\} \subseteq B^2 P_M,$$
--
--   where $B^2P_M = \{B^2x : x \in P_M\}$.
--
--   A system with a $Z_+$ constraint matrix is thus approximated, within the factor $B^2$, by a monotone two-variable-per-inequality (M2VPI) system with no more constraints than $M$ has nonzero entries. M2VPI systems are solvable in strongly polynomial time; in the paper this approximation is what makes the starting prices of each phase of the exchange-market algorithm computable in strongly polynomial time (Theorem 3.7).
--
--   **Formalization Note** The paper's theorem also states that the system is constructed in time $O(\ell(\min\{k,t\})^3)$ and that the entries of $\bar M$, $\bar b$ have polynomially bounded encoding size; these complexity claims are not formalized, and the statement is the existence the construction (13) witnesses. $k \ge 1$ is added so that $\min_{i\in[k]} b_i$ is defined. The page prints "$\bar b \in \mathbb{Q}^{l'}$" for $\mathbb{Q}^{\ell'}$. Indices are 0-based.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 15, Theorem 6.4 (proof §7, pp. 16–23)

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting

namespace LinExchangeSP.ZPlus

/-- Theorem 6.4 (p. 15), existence part: for a Z₊-matrix `M` with `ℓ` nonzero entries and `b > 0`
there is an M2VPI system `M̄x ≤ b̄` with `ℓ' ≤ ℓ` rows, `M̄`, `b̄` rational, such that
`P_M ⊆ {x ≥ 0 : M̄x ≤ b̄} ⊆ B²·P_M`, `B = ∑ⱼ bⱼ / minᵢ bᵢ`. The running time and encoding-size
clauses are not formalized. `0 < k` is needed for `B` (min over `[k]`). -/
theorem theorem_6_4 {k t : ℕ} (hk : 0 < k) (M : Matrix (Fin k) (Fin t) ℚ) (hM : IsZPlus M)
    (b : Fin k → ℚ) (hb : ∀ i, 0 < b i) :
    ∃ (l' : ℕ) (Mbar : Matrix (Fin l') (Fin t) ℚ) (bbar : Fin l' → ℚ),
      l' ≤ nnz M ∧ IsM2 Mbar ∧
      polyhedron M b ⊆ polyhedron Mbar bbar ∧
      polyhedron Mbar bbar ⊆ scale (Bconst b hk ^ 2) (polyhedron M b) := by sorry

end LinExchangeSP.ZPlus
