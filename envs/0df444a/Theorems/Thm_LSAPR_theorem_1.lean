-- Prove2me | Theorems.Thm_LSAPR_theorem_1
-- name    : LSAPR.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:19.485636+00:00
-- url     : https://prove2.me/theorems/21786bec-4639-48d5-a8ea-7013be269657
-- title:
--   Theorem 1 — $p$-th moment bound for LSA-PR under i.i.d. noise (corrected: factor $a$ in the exponent)
-- statement:
--   Let $d\ge1$, let $\pi$ be a probability measure on a measurable space $\mathsf Z$, and let $\mathbf A:\mathsf Z\to\mathbb R^{d\times d}$, $\mathbf b:\mathsf Z\to\mathbb R^d$ be measurable, with means $\bar{\mathbf A}=\int\mathbf A\,d\pi$, $\bar{\mathbf b}=\int\mathbf b\,d\pi$, centered parts $\tilde{\mathbf A}=\mathbf A-\bar{\mathbf A}$, $\tilde{\mathbf b}=\mathbf b-\bar{\mathbf b}$, and solution $\theta^\star$ of $\bar{\mathbf A}\theta=\bar{\mathbf b}$. Write $\varepsilon(z)=\tilde{\mathbf A}(z)\theta^\star-\tilde{\mathbf b}(z)$. Assume A 1 (the spectral norms of $\mathbf A(z)$ and $\tilde{\mathbf A}(z)$ are at most $\mathrm C_{\mathbf A}$ and $-\bar{\mathbf A}$ is Hurwitz), A 2 ($\|\varepsilon(z)\|\le\|\varepsilon\|_\infty$ for all $z$), and IND 1 ($(Z_k)$ is i.i.d. with law $\pi$ on a probability space). Let $Q$ be the solution of the Lyapunov equation $\bar{\mathbf A}^\top Q+Q\bar{\mathbf A}=\mathrm I$, and let $a,\alpha_\infty,\kappa_Q,b_Q,\mathrm c_{\mathbf A},\alpha_{q,\infty}$ be the constants (6), (18), (19). There exist a function $C(\kappa_Q,a,\mathrm C_{\mathbf A})$ and an exponent $k\in\mathbb N$ such that, for all such data, every real $p\ge2$, every even $n\ge2$ and every $\theta_0\in\mathbb R^d$, the following holds. Run LSA with the step size
--   $$\alpha(n,d,p)=\big(\alpha_\infty\wedge\mathrm c_{\mathbf A}/\{1+\log d\}\big)(pn^{1/2})^{-1},$$
--   and let $\bar\theta_n=(2/n)\sum_{k=n/2}^{n-1}\theta_k$. Then
--   $$\mathbb E^{1/p}\big[\|\bar{\mathbf A}(\bar\theta_n-\theta^\star)\|^p\big]\le C(\kappa_Q,a,\mathrm C_{\mathbf A})(1+\log d)^k\Big(\frac{\{\mathrm{Tr}\,\Sigma_\varepsilon\}^{1/2}p^{1/2}}{n^{1/2}}+\|\varepsilon\|_\infty\Big(\frac p{n^{3/4}}+\frac{p^2}n\Big)+p\|\theta_0-\theta^\star\|\exp\Big\{-\frac{a(\alpha_\infty\wedge\mathrm c_{\mathbf A})\sqrt n}{8p(1+\log d)}\Big\}\Big).$$
--
--   The leading term matches the central limit theorem, the remainder is of order $n^{-3/4}$, and the step size depends on the dimension only through $1/\log d$.
--
--   **Formalization Note** $\mathbb E^{1/p}[\|\cdot\|^p]$ is an `eLpNorm` in $[0,\infty]$, so an infinite moment would falsify the bound. The constant and the exponent are quantified before the dimension and the instance.
--
--   Differences from the source:
--   - correction: exp{−(α∞ ∧ c_A)√n/(8p(1 + log d))} → exp{−a(α∞ ∧ c_A)√n/(8p(1 + log d))}; reason: the printed exponent is false. Take d = 1, A ≡ 1/8, b constant, Z_k i.i.d.: A 1, A 2, IND 1 hold, ε ≡ 0, Tr Σ_ε = 0, Q = 4, κ_Q = 1, a = 1/8, α∞ ∧ c_A = 1, α(n,1,p) = 1/(p√n), and θ_k − θ⋆ = r^k(θ₀ − θ⋆) with r = 1 − 1/(8p√n). Then Ā(θ̄_n − θ⋆) = (2p/√n) r^{n/2}(1 − r^{n/2})(θ₀ − θ⋆) decays like e^{−√n/(16p)}, while the printed right side is C p‖θ₀ − θ⋆‖ e^{−√n/(8p)}, so the ratio tends to ∞ for p = 2, θ₀ ≠ θ⋆. The factor e^{−αan/8} of Theorem 2 gives the corrected exponent
--   - reading: ≲_d: inequality up to a constant that depends on κ_Q, a, C_A, and polylogarithmic factors in d (p.7) → ∃ C : ℝ → ℝ → ℝ → ℝ, ∃ k : ℕ, the factor C(κ_Q, a, C_A)(1 + log d)^k, chosen before d and the instance; reason: the strongest reading of the paper's definition; C sees nothing but κ_Q, a, C_A
--   - generalization: C_A and ‖ε‖∞ are the suprema of A 1 and A 2 → CA and εmax are any real upper bounds of those suprema; reason: the proof uses only the bounds; taking them equal to the suprema recovers the source's statement
--   - encoding: Q is the solution of the Lyapunov equation given by Proposition 1 → Q is a variable with hypothesis IsLyapunov Ā Q; reason: by Proposition 1 exactly one such Q exists, so the universally quantified statement is about that Q
--   - encoding: E^{1/p}[‖X‖^p] of a nonnegative or vector quantity → eLpNorm X (ENNReal.ofReal p) P in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound rather than make it vacuous
--   - encoding: ℝ^d with no lower bound on the dimension stated → the binder 1 ≤ d; reason: the dimension of ℝ^d is a positive integer throughout the paper; at d = 0 the space is {0}, λ_max(Q), λ_min(Q) and ‖Ā‖_Q are undefined and log d (Theorems 1, 2) is −∞, so only undefined cases are excluded
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Theorem 1, p.7; (21), p.7; definition of ≲_d, p.7; corrected by the proof, (53) p.19 and Theorem 2 p.10

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

universe u v

/-- Theorem 1, arXiv:2207.04475v2, p.7, with the factor `a` in the exponent (corrected, see the
Formalization Note): there are a function `C` of `(κ_Q, a, C_A)` and an exponent `k` such that for
every `d ≥ 1`, every model satisfying A 1, A 2, IND 1, every real `p ≥ 2`, every even `n ≥ 2` and
every `θ₀ ∈ ℝ^d`, with the step size `α(n, d, p)` of (21),
`E^{1/p}[‖Ā (θ̄_n - θ⋆)‖^p] ≤ C(κ_Q, a, C_A) (1 + log d)^k ({Tr Σ_ε}^{1/2} p^{1/2} / n^{1/2}
  + ‖ε‖∞ (p / n^{3/4} + p² / n)
  + p ‖θ₀ - θ⋆‖ exp{-a (α∞ ∧ c_A) √n / (8 p (1 + log d))})`.

**Formalization Note.** `≲_d` of p.7 is the outer `∃ C k`, before every instance. The printed
exponent has no factor `a` and is false: take `d = 1`, `A ≡ 1/8`, `b` constant, so `ε ≡ 0`,
`a = 1/8`, `α∞ ∧ c_A = 1`; the left side decays like `e^{-√n / (16 p)}`, the printed right side
like `e^{-√n / (8 p)}`. The exponent `e^{-α a n/8}` of Theorem 2 gives the corrected form. -/
theorem theorem_1 :
    ∃ (C : ℝ → ℝ → ℝ → ℝ) (k : ℕ),
      ∀ (d : ℕ), 1 ≤ d →
      ∀ (Z : Type u) [MeasurableSpace Z] (π : Measure Z) [IsProbabilityMeasure π]
        (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (A : Z → Mat d) (b : Z → Vec d) (CA εmax : ℝ) (Q : Mat d) (θstar : Vec d)
        (Zs : ℕ → Ω → Z),
        SatisfiesA1 π A CA → SatisfiesA2 π A b θstar εmax →
        IsLyapunov (Abar π A) Q → SatisfiesIND1 π P Zs →
      ∀ (p : ℝ) (n : ℕ) (θ0 : Vec d), 2 ≤ p → 2 ≤ n → Even n →
        eLpNorm
            (fun ω => matApply (Abar π A)
              (prAvg (stepSize (Abar π A) Q CA n p) A b θ0 (fun k => Zs k ω) (n / 2) n - θstar))
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal
            (C (kappaQ Q) (aQ Q) CA * (1 + Real.log d) ^ k *
              (Real.sqrt (Matrix.trace (SigmaEps π (epsNoise π A b θstar))) * Real.sqrt p
                  / Real.sqrt n
                + εmax * (p / (n : ℝ) ^ (3 / 4 : ℝ) + p ^ 2 / n)
                + p * ‖θ0 - θstar‖ *
                  Real.exp (-(aQ Q * min (alphaInf (Abar π A) Q) (cA Q CA) * Real.sqrt n)
                    / (8 * p * (1 + Real.log d))))) := by sorry

end LSAPR
