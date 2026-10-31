-- Prove2me | Theorems.Thm_OgawaNagaoka_eq2_operator_monotone
-- name    : OgawaNagaoka.eq2_operator_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:15.841199+00:00
-- url     : https://prove2.me/theorems/a3d0e255-29ab-4217-8a6a-5607db2c5e67
-- title:
--   Eq. (2): $\rho_{u_l}=(\rho_{u_l}^{1/\beta})^\beta\le(\sum_k\rho_{u_k}^{1/\beta})^\beta$
-- statement:
--   Let $\sigma_1,\dots,\sigma_M$ be positive semidefinite operators on a finite-dimensional Hilbert space and $0<\beta\le1$. Then for every $l$,
--
--   $$
--   \sigma_l=\big(\sigma_l^{1/\beta}\big)^\beta\le\Big(\sum_{k=1}^M\sigma_k^{1/\beta}\Big)^\beta .
--   $$
--
--   In the paper the $\sigma_k$ are the codeword states $\rho_{u_k}$; the inequality follows from the operator monotonicity of $x\mapsto x^\beta$ and is the key step of Lemma 1.
--
--   Differences from the source:
--   - generalization: the codeword states $\rho_{u_1},\dots,\rho_{u_M}$ → an arbitrary finite family $\sigma_k$ of positive semidefinite matrices; reason: the codeword states are positive semidefinite, so the paper's (2) is the instance $\sigma_k=\rho_{u_k}$
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
--   - encoding: operator inequality $X\le Y$ → `(Y - X).PosSemidef`; reason: this is the definition of the Loewner order
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, eq. (2), p.3

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

open scoped ComplexOrder

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, eq. (2), p.3 (proof of Lemma 1): for `0 < β ≤ 1`,
`ρ_{u_l} = (ρ_{u_l}^{1/β})^β ≤ (Σ_{k=1}^M ρ_{u_k}^{1/β})^β` for every `l`, by operator monotonicity
of `x^β`.

**Formalization Note.** Stated for an arbitrary finite family `σ_k` of positive semidefinite
matrices (the paper's `ρ_{u_k}` are such a family). `A ≤ B` is `(B - A).PosSemidef`; powers are
`matPow` (functional calculus). -/
theorem eq2_operator_monotone {K ι : Type} [Fintype K] [Fintype ι] [DecidableEq ι]
    (σ : K → Matrix ι ι ℂ) (hσ : ∀ k, (σ k).PosSemidef) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (l : K) :
    matPow (matPow (σ l) (1 / β)) β = σ l ∧
      (matPow (∑ k, matPow (σ k) (1 / β)) β - σ l).PosSemidef := by sorry

end OgawaNagaoka
