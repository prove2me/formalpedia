-- Prove2me | Theorems.Thm_GOLiQ_lemma_5
-- name    : GOLiQ.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:59.277768+00:00
-- url     : https://prove2.me/theorems/84beff24-ec7f-40b8-b24f-c80002407421
-- title:
--   Lemma 5 — gradient formula (18) via $\mathbb E[W_\infty]$ and $\mathbb E[X_\infty]$ (corrected: $U_1$ or $V_1$ atomless)
-- statement:
--   Suppose Assumptions 1 and 2 hold and $U_1$ or $V_1$ has no atoms. Then for any $(\mu,p)\in\mathcal B$, $\mathbb E[W_\infty(\mu,p)]$ is differentiable in $\mu$ and in $p$, and
--   $$\frac{\partial f}{\partial p}(\mu,p)=-\lambda(p)-p\lambda'(p)+h_0\lambda'(p)\Big(\mathbb E[W_\infty(\mu,p)]+\mathbb E[X_\infty(\mu,p)]+\frac1\mu\Big),$$
--   $$\frac{\partial f}{\partial\mu}(\mu,p)=c'(\mu)-h_0\frac{\lambda(p)}{\mu}\Big(\mathbb E[W_\infty(\mu,p)]+\mathbb E[X_\infty(\mu,p)]+\frac1\mu\Big).\tag{18}$$
--
--   The gradient of the steady-state cost is thus expressed through steady-state means of observable quantities, which is what GOLiQ estimates from data.
--
--   Differences from the source:
--   - correction: for any light-tailed U, V (Assumptions 1–2), E[W∞(µ, p)] is differentiable at every (µ, p) ∈ B and (18) holds → the same conclusion under the added hypothesis that U₁ or V₁ has no atoms; reason: as printed it is false: U ≡ 1, V uniform on {0, 2}, λ ≡ 1, c ≡ 0, h₀ = 1, B = [3/2, 3] × [1, 2] satisfy Assumptions 1–2 (η = 1, θ = 1/100, a = 1/10, γ = 10⁻⁴), yet E[W∞(µ, p)] = 0 for µ ≥ 2 and ≥ (2 − µ)/(2µ) for µ < 2, so it is not differentiable at the interior point µ = 2; the cited Lemma 7 (Glasserman, Cor. 5.3, p.74) gives the derivative only almost everywhere; without atoms the maximizer in Loynes' construction is a.s. unique and every clause holds
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - encoding: W∞(µ, p), the steady-state waiting time → Loynes' supremum sup_{n≥0} Σ_{j=1}^n (Vⱼ/µ − Uⱼ/λ(p)) on the primitives; reason: it has the stationary law; it is the coupling from the past of p.58
--   - encoding: X∞(µ, p), the steady-state observed busy period → Σ_{j=1}^ν Uⱼ/λ(p), ν the last customer before customer 0 who found the server idle, in Loynes' construction; reason: the stationary limit of recursion (7) on the same primitives
--   - encoding: partial derivatives at (µ, p) ∈ B → derivatives within [µ̲, µ̄] and [p̲, p̄], one-sided at the end points; reason: B is closed; at its edges only one-sided derivatives exist
--   - encoding: f of (2), through the steady-state queue length Q∞(µ, p) → f defined by (5), h₀λ(p)(E[W∞(µ, p)] + 1/µ) + c(µ) − pλ(p); reason: the paper's own identity (5) (Little's law, p.13) for every (µ, p) ∈ B; Q∞ is not used elsewhere
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 5, p.30

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Assumption2
import Definitions.Def_GOLiQ_Model_objective

open MeasureTheory

namespace GOLiQ

/-- **Lemma 5 (gradient formula (18))** (Chen, Liu, Hong, arXiv:2009.02911v3, p.30): under
Assumptions 1 and 2, for any `(µ, p) ∈ B`, `E[W∞(µ, p)]` is differentiable in `µ` and in `p`, and

`∂f/∂p (µ, p) = −λ(p) − pλ′(p) + h₀λ′(p) (E[W∞(µ, p)] + E[X∞(µ, p)] + 1/µ)`,
`∂f/∂µ (µ, p) = c′(µ) − h₀ (λ(p)/µ) (E[W∞(µ, p)] + E[X∞(µ, p)] + 1/µ)`.

**Formalization Note.** Derivatives are taken within the intervals `[µ̲, µ̄]` and `[p̲, p̄]`
(one-sided at their end points); `λ′`, `c′` are the derivatives within those intervals. `W∞`, `X∞`
are the Loynes constructions on the primitives, and `f` is (5).

**Correction.** The statement adds the hypothesis that `U₁` or `V₁` has no atoms. As printed (any
light-tailed `U, V`) it is false: with `U ≡ 1`, `V` uniform on `{0, 2}`, `λ ≡ 1`, `c ≡ 0`, `h₀ = 1`,
`B = [3/2, 3] × [1, 2]` (Assumption 2 holds with `η = 1`, `θ = 1/100`, `a = 1/10`, `γ = 10⁻⁴`),
`E[W∞(µ, p)] = 0` for `µ ≥ 2` and `E[W∞(µ, p)] ≥ (2 − µ)/(2µ)` for `µ < 2`, so it is not
differentiable at the interior point `µ = 2`. The cited result (Lemma 7, Glasserman's Corollary 5.3,
p.74) gives the derivative only almost everywhere in the parameter; without atoms the maximizer in
Loynes' construction is almost surely unique and the full statement holds at every point. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (η θ a γ : ℝ) (h2 : Assumption2 M Pr η θ a γ)
    (hatom : (∀ t : ℝ, Pr.P {ω | Pr.U 1 ω = t} = 0) ∨ (∀ t : ℝ, Pr.P {ω | Pr.V 1 ω = t} = 0))
    (mu p : ℝ) (hmu : mu ∈ Set.Icc M.muLo M.muHi) (hp : p ∈ Set.Icc M.pLo M.pHi) :
    (∃ d : ℝ, HasDerivWithinAt (fun mu' => M.waitMean Pr mu' p) d (Set.Icc M.muLo M.muHi) mu) ∧
    (∃ d : ℝ, HasDerivWithinAt (fun p' => M.waitMean Pr mu p') d (Set.Icc M.pLo M.pHi) p) ∧
    HasDerivWithinAt (fun p' => M.objective Pr !₂[mu, p'])
      (-M.lam p - p * M.dlam p +
        M.h0 * M.dlam p * (M.waitMean Pr mu p + M.busyMean Pr mu p + 1 / mu))
      (Set.Icc M.pLo M.pHi) p ∧
    HasDerivWithinAt (fun mu' => M.objective Pr !₂[mu', p])
      (M.dc mu - M.h0 * (M.lam p / mu) * (M.waitMean Pr mu p + M.busyMean Pr mu p + 1 / mu))
      (Set.Icc M.muLo M.muHi) mu := by sorry

end GOLiQ
