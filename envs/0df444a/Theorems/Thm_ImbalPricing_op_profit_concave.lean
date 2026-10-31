-- Prove2me | Theorems.Thm_ImbalPricing_op_profit_concave
-- name    : ImbalPricing.op_profit_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:22.705849+00:00
-- url     : https://prove2.me/theorems/dee59669-2188-4d6a-8df3-80c2059fc756
-- title:
--   Concavity of the OP profit in the own offer and first-order condition at $d=0$ (derived from Definition 4)
-- statement:
--   Under the standing assumptions of the market ($N\ge1$ LCGs with $\gamma^i>0$, $\gamma\le1$, $\alpha_2\ge\alpha_1\ge0$, mean-zero square-integrable forecast errors on a probability space), for every offer profile $d$ and every LCG $i$, let $f(x)=\Pi^i_{op}(x,d^{-i})$ be LCG $i$'s expected OP profit when it offers $x$ and the others keep $d^{-i}$. Then:
--
--   1. $f$ is concave on $\mathbb R$;
--   2. if $\alpha_1<\alpha_2$, $f$ is strictly concave on $\mathbb R$;
--   3. if all other LCGs offer $0$, then $f$ is differentiable at $0$ with $f'(0)=0$.
--
--   Together these say that, under the optimal imbalance price, offering $d^i=0$ is a best response to everybody else offering $0$, and the unique one when $\alpha_1<\alpha_2$. This is the analogue for the OP mechanism of Lemma 2 of the paper, which states concavity for the TDP mechanism; it is derived from Definition 4 (Eq. (26)) and the expected-profit form of Eq. (20), and is not printed in the paper.
--
--   Differences from the source:
--
--   - reading: profit Πⁱ = p₁L₁ⁱ + p₂ⁱL₂ⁱ (Eq. (9) prints no expectation; Eq. (20) prints p₁L₁ⁱ + E[p₂ⁱL₂ⁱ]) → expected profit Πⁱ_op = E[p₁L₁ⁱ + p^i_{2,op}L₂ⁱ]; reason: the offer is chosen in Stage 1 before ε, ν are realized, Eq. (20) and Proposition 1 take the expectation, and p₁, L₁ⁱ are deterministic, so both printed forms agree with this one
--   - reading: MC₂ 'continues only until the point where MC₂ reaches zero' (p.6) → prices and costs linear as in Eqs. (1)–(4), (8), (26), with no floor at zero; reason: every display and result of the paper uses the linear forms
--   - generalization: ε and νⁱ unbiased and bounded with ε ≥ −1, νⁱ ≥ −1 (pp.5–6) → ε and νⁱ have mean 0 and finite second moment (MemLp 2), with no bound; reason: the bounds only keep realized demand and production nonnegative and enter no formula; every bounded random variable is square integrable, so the source's case is included
--   - reading: expected productions γⁱ of N ≥ 1 LCGs with γ = Σγⁱ ≤ 1 (pp.5–6) → 0 < N, γⁱ > 0 for every i, Σγⁱ ≤ 1; reason: γⁱ is an expected production share and Eq. (10) divides by γⁱ, so γⁱ > 0 is part of the model
--   - generalization: offers dⁱ ∈ [−1, 1/γ − 1] (p.7) → concavity on all of ℝ and for every real profile d; reason: the profit is a quadratic polynomial in the offers; restricting to the box gives the source's case
--   - encoding: E[·], VAR(ɛ), Cov(νʲ, νⁱ) of random variables; LCGs i = 1, …, N → Bochner integrals against a probability measure μ, Mathlib's variance and covariance; LCGs indexed by Fin N; reason: Lean convention; under MemLp 2 these are the usual moments, same instances
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, derived from §7, Definition 4, Eq. (26), p.13 (PDF p.15) and Eq. (20), p.11 (PDF p.13); OP analogue of Lemma 2, p.10

import Mathlib
import Definitions.Def_ImbalPricing_Market
import Definitions.Def_ImbalPricing_OPMechanism

open MeasureTheory

namespace ImbalPricing

/-- **Concavity of the OP profit in the own offer, and the first-order condition at full
commitment**, derived from Definition 4, Eq. (26), p.13 (PDF p.15) and Eq. (20), p.11
(PDF p.13) of Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal Electricity Imbalance
Pricing …*, MSOM Articles in Advance (2023). Under the standing assumptions of §3.1, for every
offer profile `d` and every LCG `i`:

1. `x ↦ Πⁱ_op(d[i ↦ x])` is concave on `ℝ`;
2. it is strictly concave when `α₁ < α₂`;
3. when all other LCGs offer `0`, its derivative at `x = 0` is `0`.

**Formalization Note.** A planning derivation, the OP analogue of Lemma 2 (p.10, about the TDP
mechanism). The deviation of LCG `i` is `Function.update d i x`. -/
theorem op_profit_concave {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Market Ω N)
    (hM : M.Standing) (d : Fin N → ℝ) (i : Fin N) :
    ConcaveOn ℝ Set.univ (fun x => M.profitOP (Function.update d i x) i) ∧
      (M.α₁ < M.α₂ →
        StrictConcaveOn ℝ Set.univ (fun x => M.profitOP (Function.update d i x) i)) ∧
      HasDerivAt (fun x => M.profitOP (Function.update (0 : Fin N → ℝ) i x) i) 0 0 := by sorry

end ImbalPricing
