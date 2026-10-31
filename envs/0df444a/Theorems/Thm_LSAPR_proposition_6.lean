-- Prove2me | Theorems.Thm_LSAPR_proposition_6
-- name    : LSAPR.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:05.760887+00:00
-- url     : https://prove2.me/theorems/74e979fe-79da-4d64-9e98-7264a38a967f
-- title:
--   Proposition 6 — moment bounds for $J^{(1)}_n$ and $H^{(1)}_n$
-- statement:
--   Let $d\ge1$, let $\pi$ be a probability measure on a measurable space $\mathsf Z$, and let $\mathbf A:\mathsf Z\to\mathbb R^{d\times d}$, $\mathbf b:\mathsf Z\to\mathbb R^d$ be measurable, with means $\bar{\mathbf A}=\int\mathbf A\,d\pi$, $\bar{\mathbf b}=\int\mathbf b\,d\pi$, centered parts $\tilde{\mathbf A}=\mathbf A-\bar{\mathbf A}$, $\tilde{\mathbf b}=\mathbf b-\bar{\mathbf b}$, and solution $\theta^\star$ of $\bar{\mathbf A}\theta=\bar{\mathbf b}$. Write $\varepsilon(z)=\tilde{\mathbf A}(z)\theta^\star-\tilde{\mathbf b}(z)$. Assume A 1 (the spectral norms of $\mathbf A(z)$ and $\tilde{\mathbf A}(z)$ are at most $\mathrm C_{\mathbf A}$ and $-\bar{\mathbf A}$ is Hurwitz), A 2 ($\|\varepsilon(z)\|\le\|\varepsilon\|_\infty$ for all $z$), and IND 1 ($(Z_k)$ is i.i.d. with law $\pi$ on a probability space). Let $Q$ be the solution of the Lyapunov equation $\bar{\mathbf A}^\top Q+Q\bar{\mathbf A}=\mathrm I$, and let $a,\alpha_\infty,\kappa_Q,b_Q,\mathrm c_{\mathbf A},\alpha_{q,\infty}$ be the constants (6), (18), (19). Let $J^{(1)},H^{(1)}$ be the recursions (12), and $\mathsf D_3=2\kappa_Q\mathrm C_{\mathbf A}/a^2$, $\mathsf D_4=4\kappa_Q^{1/2}\mathrm C_{\mathbf A}\mathsf D_3/a$ the constants (48).
--
--   1. For every $\alpha\in(0,\alpha_\infty]$, real $p\ge2$ and $n\in\mathbb N$,
--   $$\mathbb E^{1/p}\big[\|J^{(1)}_n\|^p\big]\le\mathsf D_3\alpha ap^{3/2}\|\varepsilon\|_\infty.$$
--   2. For all real $2\le p\le q$, $\alpha\in(0,\alpha_{q,\infty}]$ and $n\in\mathbb N$,
--   $$\mathbb E^{1/p}\big[\|H^{(1)}_n\|^p\big]\le\mathsf D_4\alpha ap^{3/2}d^{1/q}\|\varepsilon\|_\infty.$$
--
--   Both terms are of order $\alpha$, one order smaller than $J^{(0)}_n$; this scale separation is what gives the sharp remainder of Theorem 1.
--
--   Differences from the source:
--   - generalization: C_A and ‖ε‖∞ are the suprema of A 1 and A 2 → CA and εmax are any real upper bounds of those suprema; reason: the proof uses only the bounds; taking them equal to the suprema recovers the source's statement
--   - encoding: Q is the solution of the Lyapunov equation given by Proposition 1 → Q is a variable with hypothesis IsLyapunov Ā Q; reason: by Proposition 1 exactly one such Q exists, so the universally quantified statement is about that Q
--   - encoding: E^{1/p}[‖X‖^p] of a nonnegative or vector quantity → eLpNorm X (ENNReal.ofReal p) P in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound rather than make it vacuous
--   - encoding: ℝ^d with no lower bound on the dimension stated → the binder 1 ≤ d; reason: the dimension of ℝ^d is a positive integer throughout the paper; at d = 0 the space is {0}, λ_max(Q), λ_min(Q) and ‖Ā‖_Q are undefined and log d (Theorems 1, 2) is −∞, so only undefined cases are excluded
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Proposition 6, p.9, (28), (29); (48), p.18

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- Proposition 6, arXiv:2207.04475v2, p.9: under A 1, A 2 and IND 1,
(28) for `α ∈ (0, α∞]`, real `p ≥ 2` and `n ∈ ℕ`,
`E^{1/p}[‖J^{(1)}_n‖^p] ≤ D₃ α a p^{3/2} ‖ε‖∞`; and
(29) for `2 ≤ p ≤ q`, `α ∈ (0, α_{q,∞}]` and `n ∈ ℕ`,
`E^{1/p}[‖H^{(1)}_n‖^p] ≤ D₄ α a p^{3/2} d^{1/q} ‖ε‖∞`. -/
theorem proposition_6 {d : ℕ} (hd : 1 ≤ d) {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (π : Measure Z) [IsProbabilityMeasure π] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Z → Mat d) (b : Z → Vec d) (CA εmax : ℝ) (Q : Mat d) (θstar : Vec d) (Zs : ℕ → Ω → Z)
    (hA1 : SatisfiesA1 π A CA) (hA2 : SatisfiesA2 π A b θstar εmax)
    (hQ : IsLyapunov (Abar π A) Q) (hZ : SatisfiesIND1 π P Zs) :
    (∀ (α : ℝ), 0 < α → α ≤ alphaInf (Abar π A) Q → ∀ (p : ℝ), 2 ≤ p → ∀ n : ℕ,
      eLpNorm (fun ω => J1 (Abar π A) A (epsNoise π A b θstar) α (fun k => Zs k ω) n)
          (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (D3 Q CA * α * aQ Q * p ^ (3 / 2 : ℝ) * εmax)) ∧
    (∀ (p q : ℝ), 2 ≤ p → p ≤ q → ∀ (α : ℝ), 0 < α → α ≤ alphaQInf (Abar π A) Q CA q →
      ∀ n : ℕ,
      eLpNorm (fun ω => H1 (Abar π A) A (epsNoise π A b θstar) α (fun k => Zs k ω) n)
          (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (D4 Q CA * α * aQ Q * p ^ (3 / 2 : ℝ) * (d : ℝ) ^ (1 / q) * εmax)) := by sorry

end LSAPR
