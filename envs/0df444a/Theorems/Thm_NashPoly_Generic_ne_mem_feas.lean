-- Prove2me | Theorems.Thm_NashPoly_Generic_ne_mem_feas
-- name    : NashPoly.Generic.ne_mem_feas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:55.418634+00:00
-- url     : https://prove2.me/theorems/5d04793f-8b26-4414-9900-74db71739f2a
-- title:
--   Proof of Theorem 3.2, p. 10 — every Nash equilibrium is feasible for (3.10)
-- statement:
--   Let a NEPP with polynomial multiplier expressions be given, i.e. matrix polynomials $H_i$ with $H_i(x_i)G_i(x_i)=I_{m_i}$ for every player $i$, and let $K_i\subseteq X_i$ be sets of feasible strategies of player $i$. Then every Nash equilibrium $x$ is feasible for (3.10): $x\in G$ and
--   $$f_i(v,x_{-i})-f_i(x_i,x_{-i})\ge 0\qquad\text{for all } v\in K_i,\ i\in[N].$$
--   In particular, if (3.10) is infeasible, the NEPP has no Nash equilibrium.
--
--   This justifies the "no NE" output of Step 1 of Algorithm 3.1: the cuts added by the algorithm never remove an equilibrium.
--
--   **Formalization Note** The cut sets of a run of Algorithm 3.1 consist of optimizers of (3.8), hence of feasible strategies, so they satisfy the hypothesis $K_i\subseteq X_i$.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 10, proof of Theorem 3.2

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr

namespace NashPoly.Generic

open MvPolynomial Matrix

/-- Proof of Theorem 3.2, p. 10: with polynomial multiplier expressions (`H_i G_i = I`), if
every cut set `K_i` consists of feasible strategies of player `i`, then every Nash equilibrium is
feasible for (3.10). In particular, if (3.10) is infeasible there is no Nash equilibrium. -/
theorem ne_mem_feas {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (hH : ∀ i, H i * Gmat (P.g i) = 1)
    (K : (i : Fin N) → Set (Fin (n i) → ℝ)) (hK : ∀ i, K i ⊆ P.X i) :
    P.NESet ⊆ P.Feas H K := by sorry

end NashPoly.Generic
