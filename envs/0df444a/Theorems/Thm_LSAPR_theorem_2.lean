-- Prove2me | Theorems.Thm_LSAPR_theorem_2
-- name    : LSAPR.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:08.572965+00:00
-- url     : https://prove2.me/theorems/3e35af0f-6be4-41b6-9955-9d16ef8c24b0
-- title:
--   Theorem 2 — exact-constant $p$-th moment bound for LSA-PR with an arbitrary step size
-- statement:
--   Let $d\ge1$, let $\pi$ be a probability measure on a measurable space $\mathsf Z$, and let $\mathbf A:\mathsf Z\to\mathbb R^{d\times d}$, $\mathbf b:\mathsf Z\to\mathbb R^d$ be measurable, with means $\bar{\mathbf A}=\int\mathbf A\,d\pi$, $\bar{\mathbf b}=\int\mathbf b\,d\pi$, centered parts $\tilde{\mathbf A}=\mathbf A-\bar{\mathbf A}$, $\tilde{\mathbf b}=\mathbf b-\bar{\mathbf b}$, and solution $\theta^\star$ of $\bar{\mathbf A}\theta=\bar{\mathbf b}$. Write $\varepsilon(z)=\tilde{\mathbf A}(z)\theta^\star-\tilde{\mathbf b}(z)$. Assume A 1 (the spectral norms of $\mathbf A(z)$ and $\tilde{\mathbf A}(z)$ are at most $\mathrm C_{\mathbf A}$ and $-\bar{\mathbf A}$ is Hurwitz), A 2 ($\|\varepsilon(z)\|\le\|\varepsilon\|_\infty$ for all $z$), and IND 1 ($(Z_k)$ is i.i.d. with law $\pi$ on a probability space). Let $Q$ be the solution of the Lyapunov equation $\bar{\mathbf A}^\top Q+Q\bar{\mathbf A}=\mathrm I$, and let $a,\alpha_\infty,\kappa_Q,b_Q,\mathrm c_{\mathbf A},\alpha_{q,\infty}$ be the constants (6), (18), (19). Let $\bar\theta_n=(2/n)\sum_{k=n/2}^{n-1}\theta_k$ be the Polyak–Ruppert average with burn-in $n/2$. For every real $p\ge2$, even $n\ge2$, $\alpha\in(0,\alpha_{p(1+\log d),\infty})$ and $\theta_0\in\mathbb R^d$,
--   $$(n/2)^{1/2}\,\mathbb E^{1/p}\big[\|\bar{\mathbf A}(\bar\theta_n-\theta^\star)\|^p\big]\le\mathrm C_{\mathrm{Rm},1}\{\mathrm{Tr}\,\Sigma_\varepsilon\}^{1/2}p^{1/2}+\Delta^{(\mathrm{fl})}_{n,p,\alpha}\|\varepsilon\|_\infty+\mathrm e^{-\alpha an/8}\Delta^{(\mathrm{tr})}_{n,p,\alpha}\|\theta_0-\theta^\star\|,$$
--   where $\mathrm C_{\mathrm{Rm},1}=60\mathrm e$, $\mathrm C_{\mathrm{Rm},2}=60$ and
--   $$\Delta^{(\mathrm{fl})}_{n,p,\alpha}=\frac{4\mathrm e^{1/p}\mathsf D_2(ap)^{1/2}}{(\alpha n)^{1/2}}+\mathrm e^{1/p}\mathrm C_{\mathbf A}(\mathsf D_3+\mathsf D_4)\alpha ap^{5/2}+\frac{2\mathrm C_{\mathrm{Rm},2}\,p}{n^{1/2}}+\mathrm C_{\mathbf A}\mathsf D_1(\alpha a)^{1/2}p^{3/2},$$
--   $$\Delta^{(\mathrm{tr})}_{n,p,\alpha}=\mathrm e^{1/p}\kappa_Q^{1/2}\big(4/(\alpha n^{1/2})+2^{-1/2}n^{1/2}\mathrm C_{\mathbf A}\big).$$
--
--   Theorem 1 is this bound at the step size (21).
--
--   Differences from the source:
--   - generalization: C_A and ‖ε‖∞ are the suprema of A 1 and A 2 → CA and εmax are any real upper bounds of those suprema; reason: the proof uses only the bounds; taking them equal to the suprema recovers the source's statement
--   - encoding: Q is the solution of the Lyapunov equation given by Proposition 1 → Q is a variable with hypothesis IsLyapunov Ā Q; reason: by Proposition 1 exactly one such Q exists, so the universally quantified statement is about that Q
--   - encoding: E^{1/p}[‖X‖^p] of a nonnegative or vector quantity → eLpNorm X (ENNReal.ofReal p) P in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound rather than make it vacuous
--   - encoding: ℝ^d with no lower bound on the dimension stated → the binder 1 ≤ d; reason: the dimension of ℝ^d is a positive integer throughout the paper; at d = 0 the space is {0}, λ_max(Q), λ_min(Q) and ‖Ā‖_Q are undefined and log d (Theorems 1, 2) is −∞, so only undefined cases are excluded
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Theorem 2, p.10; (53), p.19; table p.16

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- Theorem 2, arXiv:2207.04475v2, p.10, with the constants (53), p.19: under A 1, A 2, IND 1, for
real `p ≥ 2`, even `n ≥ 2`, `α ∈ (0, α_{p(1+log d),∞})` and `θ₀ ∈ ℝ^d`,
`(n/2)^{1/2} E^{1/p}[‖Ā (θ̄_n - θ⋆)‖^p] ≤ C_{Rm,1} {Tr Σ_ε}^{1/2} p^{1/2} + Δ^{(fl)}_{n,p,α} ‖ε‖∞
  + e^{-α a n/8} Δ^{(tr)}_{n,p,α} ‖θ₀ - θ⋆‖`. -/
theorem theorem_2 {d : ℕ} (hd : 1 ≤ d) {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (π : Measure Z) [IsProbabilityMeasure π] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Z → Mat d) (b : Z → Vec d) (CA εmax : ℝ) (Q : Mat d) (θstar : Vec d) (Zs : ℕ → Ω → Z)
    (hA1 : SatisfiesA1 π A CA) (hA2 : SatisfiesA2 π A b θstar εmax)
    (hQ : IsLyapunov (Abar π A) Q) (hZ : SatisfiesIND1 π P Zs)
    (p : ℝ) (hp : 2 ≤ p) (n : ℕ) (hn : 2 ≤ n) (hev : Even n)
    (α : ℝ) (hα0 : 0 < α) (hα : α < alphaQInf (Abar π A) Q CA (p * (1 + Real.log d)))
    (θ0 : Vec d) :
    ENNReal.ofReal (Real.sqrt ((n : ℝ) / 2)) *
        eLpNorm
          (fun ω => matApply (Abar π A) (prAvg α A b θ0 (fun k => Zs k ω) (n / 2) n - θstar))
          (ENNReal.ofReal p) P ≤
      ENNReal.ofReal
        (CRm1 * Real.sqrt (Matrix.trace (SigmaEps π (epsNoise π A b θstar))) * Real.sqrt p
          + DeltaFl Q CA n p α * εmax
          + Real.exp (-(α * aQ Q * n) / 8) * DeltaTr Q CA n p α * ‖θ0 - θstar‖) := by sorry

end LSAPR
