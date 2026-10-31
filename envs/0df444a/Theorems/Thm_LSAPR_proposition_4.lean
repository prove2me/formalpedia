-- Prove2me | Theorems.Thm_LSAPR_proposition_4
-- name    : LSAPR.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:09.939992+00:00
-- url     : https://prove2.me/theorems/89ee29f1-e2a9-4d9e-9964-d5c3593051a6
-- title:
--   Proposition 4 — $p$-th moment bound for the last LSA iterate
-- statement:
--   Let $d\ge1$, let $\pi$ be a probability measure on a measurable space $\mathsf Z$, and let $\mathbf A:\mathsf Z\to\mathbb R^{d\times d}$, $\mathbf b:\mathsf Z\to\mathbb R^d$ be measurable, with means $\bar{\mathbf A}=\int\mathbf A\,d\pi$, $\bar{\mathbf b}=\int\mathbf b\,d\pi$, centered parts $\tilde{\mathbf A}=\mathbf A-\bar{\mathbf A}$, $\tilde{\mathbf b}=\mathbf b-\bar{\mathbf b}$, and solution $\theta^\star$ of $\bar{\mathbf A}\theta=\bar{\mathbf b}$. Write $\varepsilon(z)=\tilde{\mathbf A}(z)\theta^\star-\tilde{\mathbf b}(z)$. Assume A 1 (the spectral norms of $\mathbf A(z)$ and $\tilde{\mathbf A}(z)$ are at most $\mathrm C_{\mathbf A}$ and $-\bar{\mathbf A}$ is Hurwitz), A 2 ($\|\varepsilon(z)\|\le\|\varepsilon\|_\infty$ for all $z$), and IND 1 ($(Z_k)$ is i.i.d. with law $\pi$ on a probability space). Let $Q$ be the solution of the Lyapunov equation $\bar{\mathbf A}^\top Q+Q\bar{\mathbf A}=\mathrm I$, and let $a,\alpha_\infty,\kappa_Q,b_Q,\mathrm c_{\mathbf A},\alpha_{q,\infty}$ be the constants (6), (18), (19). For real $2\le p\le q$, $\alpha\in(0,\alpha_{q,\infty}]$, $n\in\mathbb N$ and $\theta_0\in\mathbb R^d$, the LSA iterates (1) satisfy
--   $$\mathbb E^{1/p}\big[\|\theta_n-\theta^\star\|^p\big]\le d^{1/q}\kappa_Q^{1/2}(1-\alpha a/4)^n\|\theta_0-\theta^\star\|+d^{1/q}\mathsf D_2\sqrt{\alpha ap}\,\|\varepsilon\|_\infty,$$
--   where $\mathsf D_2=(2\kappa_Q)^{1/2}a^{-1}(1+4\kappa_Q^{1/2}\mathrm C_{\mathbf A}a^{-1})$ is the constant (45).
--
--   The bound shows exponential forgetting of the initial condition plus a fluctuation of order $\sqrt\alpha$.
--
--   Differences from the source:
--   - generalization: p, q ∈ ℕ → p, q real with 2 ≤ p ≤ q; reason: the proof of Theorem 2 applies it with q = p(1 + log d), and the proof in B.2 uses only Propositions 2 and 3, which hold for real exponents; natural p, q are a special case
--   - generalization: C_A and ‖ε‖∞ are the suprema of A 1 and A 2 → CA and εmax are any real upper bounds of those suprema; reason: the proof uses only the bounds; taking them equal to the suprema recovers the source's statement
--   - encoding: Q is the solution of the Lyapunov equation given by Proposition 1 → Q is a variable with hypothesis IsLyapunov Ā Q; reason: by Proposition 1 exactly one such Q exists, so the universally quantified statement is about that Q
--   - encoding: E^{1/p}[‖X‖^p] of a nonnegative or vector quantity → eLpNorm X (ENNReal.ofReal p) P in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound rather than make it vacuous
--   - encoding: ℝ^d with no lower bound on the dimension stated → the binder 1 ≤ d; reason: the dimension of ℝ^d is a positive integer throughout the paper; at d = 0 the space is {0}, λ_max(Q), λ_min(Q) and ‖Ā‖_Q are undefined and log d (Theorems 1, 2) is −∞, so only undefined cases are excluded
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Proposition 4, p.8, (24); (45), p.17

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- Proposition 4, arXiv:2207.04475v2, p.8, (24): under A 1, A 2 and IND 1, for `2 ≤ p ≤ q`,
`α ∈ (0, α_{q,∞}]`, `n ∈ ℕ` and `θ₀ ∈ ℝ^d`,
`E^{1/p}[‖θ_n - θ⋆‖^p] ≤ d^{1/q} κ_Q^{1/2} (1 - α a/4)^n ‖θ₀ - θ⋆‖ + d^{1/q} D₂ √(α a p) ‖ε‖∞`.

**Formalization Note.** The page has `p, q ∈ ℕ`; here `p, q` are real, as in the application
`q = p (1 + log d)` of the proof of Theorem 2 (p.20). -/
theorem proposition_4 {d : ℕ} (hd : 1 ≤ d) {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (π : Measure Z) [IsProbabilityMeasure π] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Z → Mat d) (b : Z → Vec d) (CA εmax : ℝ) (Q : Mat d) (θstar : Vec d) (Zs : ℕ → Ω → Z)
    (hA1 : SatisfiesA1 π A CA) (hA2 : SatisfiesA2 π A b θstar εmax)
    (hQ : IsLyapunov (Abar π A) Q) (hZ : SatisfiesIND1 π P Zs)
    (p q : ℝ) (hp : 2 ≤ p) (hpq : p ≤ q)
    (α : ℝ) (hα0 : 0 < α) (hα : α ≤ alphaQInf (Abar π A) Q CA q) (n : ℕ) (θ0 : Vec d) :
    eLpNorm (fun ω => lsaIter α A b θ0 (fun k => Zs k ω) n - θstar) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((d : ℝ) ^ (1 / q) * Real.sqrt (kappaQ Q) * (1 - α * aQ Q / 4) ^ n *
          ‖θ0 - θstar‖
        + (d : ℝ) ^ (1 / q) * D2 Q CA * Real.sqrt (α * aQ Q * p) * εmax) := by sorry

end LSAPR
