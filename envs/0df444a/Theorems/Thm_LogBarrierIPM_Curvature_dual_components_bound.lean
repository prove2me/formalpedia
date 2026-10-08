-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_dual_components_bound
-- name    : LogBarrierIPM.Curvature.dual_components_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:53.308615+00:00
-- url     : https://prove2.me/theorems/12d32d56-bfdb-4c63-ae72-7a6fa434cb72
-- title:
--   Proof of Theorem 25, first claim — on $[0,2]$ the dual components of $\mathcal C^{\mathrm{trop}}(\lambda)$ are $\le\max(0,\lambda-1)$
-- statement:
--   Let $r\ge1$ and let $\mathcal C^{\mathrm{trop}}(\lambda)=(x^\lambda,w^\lambda,s^\lambda,y^\lambda)$ be the tropical central path of $\mathbf{LW}_r$ (Propositions 20, 21 and the identity (20)). For every $\lambda\in[0,2]$:
--
--   1. every primal component is at least $\min(1,\lambda)$: $x^\lambda_j\ge\min(1,\lambda)$ for $1\le j\le 2r$ and $w^\lambda_i\ge\min(1,\lambda)$ for $1\le i\le 3r-1$;
--   2. every dual component is at most $\max(0,\lambda-1)$:
--   $$s^\lambda_j\le\max(0,\lambda-1)\quad(1\le j\le2r),\qquad y^\lambda_i\le\max(0,\lambda-1)\quad(1\le i\le 3r-1).$$
--
--   Hence on $[0,2]$ the dual components are dominated by the primal ones, which is why it suffices to estimate the curvature of the primal central path.
--
--   **Formalization Note** The paper states the dual bound as the claim and the primal bound as its justification; both are in the conclusion. Coordinates use the paper's 1-based indices.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 23, proof of Theorem 25, second paragraph (unnumbered claim)

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TropicalCentralPathLW

namespace LogBarrierIPM.Curvature

/-- Proof of Theorem 25, first claim (p. 23). For `λ ∈ [0, 2]`, every primal component of
`C^trop(λ)` (for `LW_r`) is `≥ min(1, λ)` and every dual component is `≤ max(0, λ − 1)`. -/
theorem dual_components_bound (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) (h0 : 0 ≤ lam) (h2 : lam ≤ 2) :
    (∀ i : ℕ, 1 ≤ i → i ≤ 2 * r →
      min 1 lam ≤ tropX lam i ∧ tropS lam i ≤ max 0 (lam - 1)) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 3 * r - 1 →
      min 1 lam ≤ tropW lam i ∧ tropY lam i ≤ max 0 (lam - 1)) := by sorry

end LogBarrierIPM.Curvature
