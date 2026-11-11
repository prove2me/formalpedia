-- Prove2me | Theorems.Thm_OptLocalHamSim_eq_34
-- name    : OptLocalHamSim.eq_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:51.346993+00:00
-- url     : https://prove2.me/theorems/37fae3de-5e0f-49d1-97df-7f7d64583b76
-- title:
--   Eq. (34) — Dyson expansion $E(h)=\sum_k\sum_{\lambda,q\ge p}\prod_i\frac{-ic_{\lambda_i}(i\omega_{\lambda_i})^{q_i}h^{q_i+1}}{q_i!\,b_i}P_{\lambda_k}\cdots P_{\lambda_1}$
-- statement:
--   Let $(c_\lambda,\omega_\lambda,P_\lambda)_{\lambda<A}$ be a finite table, $p\ge0$, and let $E$ solve $E'(s)=-iK(s)E(s)$, $E(0)=I$, where $K(s)=\sum_\lambda c_\lambda e^{i\omega_\lambda s}P_\lambda$ has the expansion (26) (its Taylor coefficients below order $p$ vanish). Then for $h>0$
--
--   $$
--   E(h)=\sum_{k=0}^\infty\sum_{\substack{\lambda_1,\dots,\lambda_k\in\{0,\dots,A-1\}\\ q_1,\dots,q_k\ge p}}\Bigl(\prod_{i=1}^k\frac{-ic_{\lambda_i}(i\omega_{\lambda_i})^{q_i}h^{q_i+1}}{q_i!\,b_i}\Bigr)P_{\lambda_k}\cdots P_{\lambda_1},\qquad b_i=\sum_{a\le i}(q_a+1),
--   $$
--
--   and the series converges absolutely.
--
--   The expansion expresses each microstep correction as a series of ordered Pauli insertions with explicit coefficients.
--
--   **Formalization Note** The index is $(k,\lambda,J)$ with $q_i=p+J_i$; absolute convergence is summability of the operator norms.
--
--   Differences from the source:
--   - generalization: the residual table of Lemma 7 with Pauli strings P_λ → any finite table with arbitrary matrices P_λ and any p; reason: the derivation uses only (25)–(26); Lemma 7's table is one instance
--   - encoding: q₁,…,q_k ≥ p → q_i = p + J_i with J_i ∈ ℕ; reason: the same index set
--   - encoding: All termwise integrations and products are justified by absolute convergence → the operator norms of the terms are summable; reason: absolute convergence of the series
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), eq. (34), p.17

import Mathlib
import Definitions.Def_OptLocalHamSim_LCUData

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Eq. (34)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.17: the Dyson expansion of the residual correction,
E(h) = ∑_{k=0}^∞ ∑_{λ₁,…,λ_k ∈ {0,…,A−1}, q₁,…,q_k ≥ p}
(∏_{i=1}^k −ic_{λ_i}(iω_{λ_i})^{q_i}h^{q_i+1}/(q_i! b_i)) P_{λ_k} ⋯ P_{λ₁}, with all termwise
operations justified by absolute convergence.

**Formalization Note** Stated for any finite table `(c_λ, ω_λ, P_λ)` with arbitrary matrices `P_λ`,
any `p`, and any `E` solving (25) whose generator has the form (26) (`SolvesResidual`). The index
`(k, λ, J)` has `q_i = p + J_i`; the conclusion is absolute summability (in operator norm) and the sum. -/
theorem eq_34 {n : Type} [Fintype n] [DecidableEq n] (A : ℕ) (c : Fin A → ℂ) (ω : Fin A → ℝ)
    (P : Fin A → Matrix n n ℂ) (p : ℕ) (E : ℝ → Matrix n n ℂ) (hE : SolvesResidual c ω P p E)
    (h : ℝ) (hh : 0 < h) :
    Summable (fun x => ‖dysonTerm c ω P p h x‖) ∧ HasSum (dysonTerm c ω P p h) (E h) := by sorry

end OptLocalHamSim
