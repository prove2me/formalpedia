-- Prove2me | Theorems.Thm_LSAPR_proposition_2
-- name    : LSAPR.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:07.20327+00:00
-- url     : https://prove2.me/theorems/0d80ef81-6be8-4d76-9285-094fced1e63c
-- title:
--   Proposition 2 — exponential stability of the random matrix product $\Gamma^{(\alpha)}_{1:n}$
-- statement:
--   Let $d\ge1$, let $\pi$ be a probability measure on a measurable space $\mathsf Z$, and let $\mathbf A:\mathsf Z\to\mathbb R^{d\times d}$ be measurable with mean $\bar{\mathbf A}=\int\mathbf A\,d\pi$ and centered part $\tilde{\mathbf A}=\mathbf A-\bar{\mathbf A}$. Assume A 1 (the spectral norms of $\mathbf A(z)$ and $\tilde{\mathbf A}(z)$ are at most $\mathrm C_{\mathbf A}$ and $-\bar{\mathbf A}$ is Hurwitz) and IND 1 ($(Z_k)$ is i.i.d. with law $\pi$ on a probability space). Let $Q$ be the solution of the Lyapunov equation $\bar{\mathbf A}^\top Q+Q\bar{\mathbf A}=\mathrm I$, and let $a,\alpha_\infty,\kappa_Q,b_Q,\mathrm c_{\mathbf A},\alpha_{q,\infty}$ be the constants (6), (18), (19). For real $2\le p\le q$ and $n\ge1$, the product $\Gamma^{(\alpha)}_{1:n}=(\mathrm I-\alpha\mathbf A(Z_n))\cdots(\mathrm I-\alpha\mathbf A(Z_1))$ satisfies, for every $\alpha\in(0,\alpha_\infty]$,
--   $$\mathbb E^{1/p}\big[\|\Gamma^{(\alpha)}_{1:n}\|^p\big]\le\sqrt{\kappa_Q}\,d^{1/q}\big(1-a\alpha+(q-1)b_Q^2\alpha^2\big)^{n/2},$$
--   and, for every $\alpha\in(0,\alpha_{q,\infty}]$,
--   $$\mathbb E^{1/p}\big[\|\Gamma^{(\alpha)}_{1:n}\|^p\big]\le\sqrt{\kappa_Q}\,d^{1/q}(1-a\alpha/2)^{n/2}.$$
--
--   The free parameter $q\ge p$ trades dimension dependence against step size: $q$ of order $\log d$ removes the factor $d^{1/q}$ at the price of a step size of order $1/\log d$.
--
--   Differences from the source:
--   - generalization: C_A = sup_z ‖A(z)‖ ∨ sup_z ‖Ã(z)‖ → CA is any real upper bound of both suprema; reason: the proof uses only the bound; taking CA equal to the supremum recovers the source's statement
--   - encoding: Q is the solution of the Lyapunov equation given by Proposition 1 → Q is a variable with hypothesis IsLyapunov Ā Q; reason: by Proposition 1 exactly one such Q exists, so the universally quantified statement is about that Q
--   - encoding: E^{1/p}[‖X‖^p] of a nonnegative or vector quantity → eLpNorm X (ENNReal.ofReal p) P in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound rather than make it vacuous
--   - encoding: A 1 and IND 1 with Ā the mean of A(Z₁) (p.1) → SatisfiesA1 with Ā defined as ∫ A dπ; reason: A 2 and p.1 identify Ā with that integral, and the Lean definition of A 1 uses it
--   - encoding: ℝ^d with no lower bound on the dimension stated → the binder 1 ≤ d; reason: the dimension of ℝ^d is a positive integer throughout the paper; at d = 0 the space is {0}, λ_max(Q), λ_min(Q) and ‖Ā‖_Q are undefined and log d (Theorems 1, 2) is −∞, so only undefined cases are excluded
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Proposition 2, p.6

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- Proposition 2 (Durmus et al. 2021a, Corollary 1), arXiv:2207.04475v2, p.6: exponential
stability of the random matrix product `Γ^{(α)}_{1:n}` under A 1 and IND 1, for real
`2 ≤ p ≤ q` and `n ≥ 1`. The first bound holds for `α ∈ (0, α∞]`, the second, (20), for
`α ∈ (0, α_{q,∞}]`.

**Formalization Note.** `E^{1/p}[‖Γ‖^p]` is `eLpNorm` of the spectral norm of `Γ`, in `ℝ≥0∞`, so
an infinite moment would falsify the bound. `Q` is the solution of the Lyapunov equation of
Proposition 1, and `CA` is an upper bound of the supremum of A 1. -/
theorem proposition_2 {d : ℕ} (hd : 1 ≤ d) {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (π : Measure Z) [IsProbabilityMeasure π] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Z → Mat d) (CA : ℝ) (Q : Mat d) (Zs : ℕ → Ω → Z)
    (hA1 : SatisfiesA1 π A CA) (hQ : IsLyapunov (Abar π A) Q) (hZ : SatisfiesIND1 π P Zs)
    (p q : ℝ) (hp : 2 ≤ p) (hpq : p ≤ q) (n : ℕ) (hn : 1 ≤ n) :
    (∀ α : ℝ, 0 < α → α ≤ alphaInf (Abar π A) Q →
      eLpNorm (fun ω => matNorm (Gamma α A (fun k => Zs k ω) 1 n)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Real.sqrt (kappaQ Q) * (d : ℝ) ^ (1 / q) *
          (1 - aQ Q * α + (q - 1) * bQ Q CA ^ 2 * α ^ 2) ^ ((n : ℝ) / 2))) ∧
    (∀ α : ℝ, 0 < α → α ≤ alphaQInf (Abar π A) Q CA q →
      eLpNorm (fun ω => matNorm (Gamma α A (fun k => Zs k ω) 1 n)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Real.sqrt (kappaQ Q) * (d : ℝ) ^ (1 / q) *
          (1 - aQ Q * α / 2) ^ ((n : ℝ) / 2))) := by sorry

end LSAPR
