-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_59_60_corrected
-- name    : OTCChain.Equilibrium.eq_59_60_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:37.851615+00:00
-- url     : https://prove2.me/theorems/0d62ef06-bedd-4e72-b6a8-4a1b538284b2
-- title:
--   (58)–(60) corrected, proof of Theorem 1, Step I, p. 37 (PDF 40) — the densities between the cutoffs, and existence of the steady state
-- statement:
--   Let the standing assumptions of the model hold and let $0 < \Delta_b < \Delta_s < \bar\Delta$. Write $A(\Delta) = N - NF(\Delta) - X - \kappa/\lambda$ and $R(\Delta) = \sqrt{A(\Delta)^2 + 4\frac{\kappa}{\lambda}(N-X)[1-F(\Delta)]}$.
--
--   1. The candidate densities (55)–(63), with the corrected middle branch below, form a steady state for the cutoffs $\Delta_b$, $\Delta_s$ (they satisfy (12)–(19)).
--   2. Every steady state for these cutoffs satisfies, for every $\Delta \in (\Delta_b,\Delta_s)$: $\mu_n(\Delta) = \mu_h(\Delta) = 0$ (58),
--   $$\int_\Delta^{\bar\Delta}\mu_b(x)\,dx = \frac{A(\Delta)}{2} + \frac{R(\Delta)}{2},$$
--   and
--   $$\mu_b(\Delta) = \frac{Nf(\Delta)}{2}\Big[1 + \frac{A(\Delta) + 2\kappa(N-X)/(\lambda N)}{R(\Delta)}\Big],\qquad \mu_s(\Delta) = Nf(\Delta) - \mu_b(\Delta).$$
--
--   **Correction.** The paper prints (60) as $\mu_b = \frac{Nf}{2}[1 + A/R]$ and (59) as $\mu_s = \frac{Nf}{2}[1 - A/R]$, without the term $2\kappa(N-X)/(\lambda N)$. As printed they violate (18) and $N_b = \int\mu_b$: for $f \equiv 1$ on $[0,1]$, $N = 3$, $X = 1$, $\lambda = 5$, $\kappa = 1$, $\Delta_b = 0.3$, $\Delta_s = 0.7$, the printed densities give $\int\mu_b \approx 0.976$ while (66) gives $N_b \approx 1.145$. The corrected densities are what the paper's own derivation (67)–(71) produces: $\int_\Delta^{\bar\Delta}\mu_b$ solves the quadratic (65) with $\Delta_b$ replaced by $\Delta$, and $\mu_b$ is minus its derivative.
--
--   Item 1 is the existence half of Step I, item 2 its uniqueness half for the middle region.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 37 (PDF 40), proof of Theorem 1, Step I, (58)–(60), derived pp. 38–39 (PDF 41–42) via (67)–(71); (59)–(60) corrected

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (58) and (59)–(60) **corrected**, proof of Theorem 1, Step I, p. 37 (derived on pp. 38–39
via (67)–(71)), together with the existence half of Step I. For cutoffs `0 < ∆b < ∆s < ∆̄`:
1. the candidate densities (55)–(63), with the corrected middle branch, form a steady state;
2. in every steady state, on `(∆b, ∆s)`: `μn = μh = 0`, `∫_∆^∆̄ μb = NbOf(F ∆)` (that is, (66)
   with `∆b` replaced by `∆`), and, with `A = N − N F(∆) − X − κ/λ`,
   `R = √(A² + 4(κ/λ)(N − X)[1 − F(∆)])`,
   `μb(∆) = (N f(∆)/2)[1 + (A + 2κ(N − X)/(λN))/R]` and `μs(∆) = N f(∆) − μb(∆)`.
The paper prints (59)–(60) without the term `2κ(N − X)/(λN)`; as printed they violate (18). -/
theorem eq_59_60_corrected (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb)
    (h1 : Δb < Δs) (h2 : Δs < M.Δbar) :
    IsSteadyState M Δb Δs (candDensities M Δb Δs) ∧
    ∀ μ : Densities, IsSteadyState M Δb Δs μ → ∀ Δ ∈ Ioo Δb Δs,
      μ.μn Δ = 0 ∧ μ.μh Δ = 0 ∧
      (∫ x in Δ..M.Δbar, μ.μb x) = NbOf M (M.F Δ) ∧
      μ.μb Δ = M.N * M.f Δ / 2 *
        (1 + (M.N - M.N * M.F Δ - M.X - M.κ / M.lam + 2 * M.κ * (M.N - M.X) / (M.lam * M.N)) /
          Real.sqrt ((M.N - M.N * M.F Δ - M.X - M.κ / M.lam) ^ 2
            + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - M.F Δ))) ∧
      μ.μs Δ = M.N * M.f Δ - μ.μb Δ := by sorry

end OTCChain.Equilibrium
