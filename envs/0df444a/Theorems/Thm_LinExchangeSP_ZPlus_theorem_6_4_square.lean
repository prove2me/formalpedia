-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_theorem_6_4_square
-- name    : LinExchangeSP.ZPlus.theorem_6_4_square
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:32.957459+00:00
-- url     : https://prove2.me/theorems/00b6220b-cc58-4d52-ac61-8d8ab208adbf
-- title:
--   §7, p. 16 — Theorem 6.4 in the reduced case k = t, M_ii > 0
-- statement:
--   Let $t \ge 1$, let $M \in \mathcal{Z}_+(t,t)$ be a square $Z_+$-matrix whose diagonal entries are all positive, and let $\gamma \in \mathbb{Q}^t$ with $\gamma > 0$. Write $P_M = \{\bar p \in \mathbb{R}^t : M\bar p \le \gamma,\ \bar p \ge 0\}$, let $\ell$ be the number of nonzero entries of $M$, and $B = \sum_{j=1}^t\gamma_j/\min_{i\in[t]}\gamma_i$. Then there are $\ell' \le \ell$, a matrix $\bar M \in \mathcal{M}_2(\ell',t)$ and $\bar\gamma \in \mathbb{Q}^{\ell'}$ such that
--
--   $$P_M \subseteq \{\bar p \in \mathbb{R}^t : \bar M\bar p \le \bar\gamma,\ \bar p \ge 0\} \subseteq B^2 P_M.$$
--
--   This is the case of Theorem 6.4 to which §7 reduces the general one (p. 16): rows beyond the $t$-th, zero columns and rows and columns with a zero diagonal entry can be removed. Sections 7.2–7.3 construct the system (13) and prove both containments in this case.
--
--   **Formalization Note** As for Theorem 6.4, the running time $O(\ell t^3)$ and the encoding-size bound are not formalized; the statement is the existence the construction (13) witnesses. $\bar M$ and $\bar\gamma$ are rational, $B^2P_M$ is the image $\{B^2x : x \in P_M\}$.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 16, §7, second paragraph (reduction to k = t, M_ii > 0); construction (13) p. 19, proof pp. 19–23

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting

namespace LinExchangeSP.ZPlus

/-- §7, p. 16, second paragraph: Theorem 6.4 in the reduced case `k = t` with all diagonal entries
`M_ii > 0`, for the right-hand side `γ > 0`; `B = ∑ⱼ γⱼ / minᵢ γᵢ`. -/
theorem theorem_6_4_square {t : ℕ} (ht : 0 < t) (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) :
    ∃ (l' : ℕ) (Mbar : Matrix (Fin l') (Fin t) ℚ) (γbar : Fin l' → ℚ),
      l' ≤ nnz M ∧ IsM2 Mbar ∧
      polyhedron M γ ⊆ polyhedron Mbar γbar ∧
      polyhedron Mbar γbar ⊆ scale (Bconst γ ht ^ 2) (polyhedron M γ) := by sorry

end LinExchangeSP.ZPlus
