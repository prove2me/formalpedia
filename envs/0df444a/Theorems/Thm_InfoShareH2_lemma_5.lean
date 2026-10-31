-- Prove2me | Theorems.Thm_InfoShareH2_lemma_5
-- name    : InfoShareH2.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:19.448792+00:00
-- url     : https://prove2.me/theorems/574500ca-5afc-41cb-b82d-7a742464cb16
-- title:
--   Lemma 5 — $\tilde C(Q)$ of (41) is strictly convex in $(\theta_1,\theta_2,\dots)$
-- statement:
--   Let $\sigma_\epsilon,\sigma>0$. For a real square-summable sequence $\theta=(\theta_1,\theta_2,\dots)$ whose series $\sum_{n\ge1}\theta_n$ converges, put $\theta_0=-\sum_{n\ge1}\theta_n$ and $Q_\theta(z)=\exp\bigl(\sum_{n\ge0}\theta_nz^n\bigr)$, and let
--
--   $$\tilde C(Q)=S_1(Q)+\max\Bigl(-\frac12\log\frac{\sigma/\sigma_\epsilon}{|Q(0)|},\,0\Bigr)\qquad(41).$$
--
--   Then $\theta\mapsto\tilde C(Q_\theta)$ is strictly convex: for distinct such $\theta,\theta'$ with $S_1(Q_\theta),S_1(Q_{\theta'})<\infty$ and every $s\in(0,1)$,
--
--   $$\tilde C\bigl(Q_{s\theta+(1-s)\theta'}\bigr)<s\,\tilde C(Q_\theta)+(1-s)\,\tilde C(Q_{\theta'}).$$
--
--   Strict convexity is what makes the first-order condition in the proof of Theorem 2 identify the optimal outer factor $(1+z)/2$.
--
--   Differences from the source:
--   - reading: "Under Assumption 2 … with respect to {θ₁, θ₂, …}" with "θ₀ = −∑_{n≥1} θ_n according to Assumption 1" → θ real and square summable with convergent ∑θ_n, θ₀ := −∑_{n≥1}θ_n, Q_θ = exp(∑ θ_n zⁿ); reason: the parametrization of p.28
--   - encoding: strict convexity of C̃, which may be +∞ → strict inequality on the effective domain {S1 < ∞}, values in [0, ∞]; reason: standard meaning for an extended-valued function
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Lemma 5, p.28 (proof §9.12, pp.47–50); (41) p.27

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Lemma 5 (strict convexity of `C̃`).**
SSRN 4319721 (v. 2024-01-20), Lemma 5, p.28 (proof §9.12, pp.47–50). "Under Assumption 2, the
objective `C̃(Q)` in (41) is strictly convex with respect to `{θ_1, θ_2, …}`."

The parametrization is that of p.28: `θ = (θ_1, θ_2, …)` real and square summable (Assumption 2),
`θ_0 = −∑_{n≥1} θ_n` ("according to Assumption 1"), `Q_θ = exp(∑_{n≥0} θ_n zⁿ)`; here
`t k = θ_{k+1}`.

**Formalization Note** `C̃` takes values in `ℝ≥0∞` because `S1(Q)` may be infinite. Strict convexity
of an extended-valued function is stated on its effective domain: for distinct admissible `θ, θ'`
with `S1(Q_θ), S1(Q_θ') < ∞` and `s ∈ (0, 1)`,
`C̃(Q_{sθ+(1−s)θ'}) < s C̃(Q_θ) + (1 − s) C̃(Q_θ')`. -/
theorem lemma_5 (σε σ : ℝ) (hσε : 0 < σε) (hσ : 0 < σ) (t t' : ℕ → ℝ)
    (ht : Summable (fun k => t k ^ 2)) (ht' : Summable (fun k => t' k ^ 2))
    (hct : ∃ L : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N, t k) atTop (𝓝 L))
    (hct' : ∃ L : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N, t' k) atTop (𝓝 L))
    (hne : t ≠ t') (hS : S1 (QOfTheta t) ≠ ⊤) (hS' : S1 (QOfTheta t') ≠ ⊤)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Ctilde σε σ (QOfTheta (s • t + (1 - s) • t')) <
      ENNReal.ofReal s * Ctilde σε σ (QOfTheta t) +
        ENNReal.ofReal (1 - s) * Ctilde σε σ (QOfTheta t') := by sorry

end InfoShareH2
