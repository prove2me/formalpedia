-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_proposition_2_seller_payoff_reversals
-- name    : InfoBargaining.SellerPayoff.proposition_2_seller_payoff_reversals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:24:26.538052+00:00
-- url     : https://prove2.me/theorems/d6a5b9c9-587e-4b8c-b02a-d9eeddcd1b04
-- title:
--   Proposition 2: the seller's payoff rises in $\theta_s$ except a fall at $1-\tilde\theta$; $U_s^*$ falls in $c$ except a rise at $c_l$; $V_s^*$ rises in $c$ except a fall at $c_h$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   The seller's equilibrium expected payoffs are $U_s^*=\theta_sA(\alpha^*,c)$ when $c$ is a material cost and $V_s^*=c+\theta_sA(\alpha^*,c)$ when $c$ is an opportunity cost, with $\alpha^*$ the buyer's optimal information at $\theta_b=1-\theta_s$ and the linear cost $k(\alpha)=\bar k(\alpha-\underline\alpha)/(\bar\alpha-\underline\alpha)$.
--
--   **Proposition 2.** Consider any of the four focal distributions (uniform, exponential, logistic, modified pareto), with prior mean $\hat u$.
--
--   1. For all $0<\underline\alpha<\bar\alpha<1$ and $\bar k>0$:
--      - **(i)** for every admissible cost $c$ there is $\tilde\theta\in(0,1]$ with $\alpha^*=\bar\alpha \iff \tilde\theta<1-\theta_s$ (Corollary 1 (i)) such that, for $0<\theta_1<\theta_2<1$, if $U_s^*(\theta_2)<U_s^*(\theta_1)$ or $V_s^*(\theta_2)<V_s^*(\theta_1)$ then $\theta_1<1-\tilde\theta\le\theta_2$; and $U_s^*$, $V_s^*$ are continuous in $\theta_s$ at every $\theta_s\in(0,1)$ other than $1-\tilde\theta$;
--      - **(ii)–(iii)** for every $\theta_s\in(0,1)$ there are $c_l\le\hat u\le c_h$ with $\alpha^*=\bar\alpha\iff c_l<c<c_h$ for admissible $c$ (Corollary 1 (ii)) such that, for admissible $c_1<c_2$,
--      $$U_s^*(c_1)<U_s^*(c_2)\ \Rightarrow\ c_1\le c_l<c_2,\qquad V_s^*(c_2)<V_s^*(c_1)\ \Rightarrow\ c_1<c_h\le c_2,$$
--      and $U_s^*$, $V_s^*$ are continuous in $c$ at every admissible $c\notin\{c_l,c_h\}$.
--   2. **(may, i)** For some admissible $\underline\alpha,\bar\alpha,\bar k,c$ and $\theta_1<\theta_2$, both $U_s^*$ and $V_s^*$ fall from $\theta_1$ to $\theta_2$.
--   3. **(may, ii)** For some admissible parameters and costs $c_1<c_2$, $U_s^*(c_1)<U_s^*(c_2)$.
--   4. **(may, iii)** For some admissible parameters and costs $c_1<c_2$, $V_s^*(c_2)<V_s^*(c_1)$.
--
--   In words: the seller's payoff increases with its bargaining power and $V_s^*$ with its opportunity cost, and $U_s^*$ decreases with its material cost, except for a single jump in the opposite direction at the threshold where the buyer switches between minimal and maximal information; and each such jump actually occurs for every focal distribution. Raising the seller's bargaining power or its outside option can make it worse off, because the buyer stops investing in information and the total pie shrinks.
--
--   Differences from the source:
--   - reading: α∗, the solution to (6) → optimalInfo, the least maximizer of (6) on [α̲, ᾱ]; reason: (6) can have ties (uniform prior, c = 1/2: A(α, 1/2) = α/8); Corollary 1 sends every tie to α̲
--   - reading: increases with t, but may decrease discontinuously at t₀ (and mirror forms in (ii), (iii)) → every decrease (increase in (ii)) between t₁ < t₂ straddles t₀ with the half-open sides θ₁ < 1 − θ̃ ≤ θ₂, c₁ ≤ c_l < c₂, c₁ < c_h ≤ c₂; continuity at every other point of the domain; and for every focal prior some admissible parameters with an actual reversal; reason: monotone on each side of t₀ with a jump only at t₀, and 'may' as possibility; the half-open sides follow the corollary's tie-break α∗ = α̲ at θ_b = θ̃, c = c_l, c = c_h
--   - reading: increases / decreases → weak monotonicity (the straddle clauses); reason: strict monotonicity is false: uniform prior, c = 3/4, α̲ = 1/5 gives A(α̲, c) = 0, so U_s∗ ≡ 0 for θ_s ≥ 1 − θ̃
--   - reading: θ̃, c_l, c_h of Corollary 1 (not given in closed form) → existential θ̃ ∈ (0, 1] (after c) and c_l ≤ û ≤ c_h (after θ_s), bound together with Corollary 1's characterization of α∗; reason: the characterization pins the thresholds; without it the straddle clauses would be vacuous
--   - reading: θ_s, θ_b ∈ (0, 1), θ_s + θ_b = 1 (p. 7); [α̲, ᾱ] ⊆ (0, 1), k̄ = k(ᾱ) > 0 = k(α̲) (p. 8); c > 0 (p. 6), c ∈ (u̲, ū) (p. 7) → explicit hypotheses 0 < α̲ < ᾱ < 1, 0 < k̄, θ ∈ (0, 1), c ∈ P.costDomain, θ_b = 1 − θ_s; reason: the section's standing assumptions; α̲ < ᾱ because k(α̲) = 0 < k̄ = k(ᾱ) and the linear k divides by ᾱ − α̲
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), Proposition 2, p. 14; U_s∗, V_s∗ p. 12; linear cost and four focal distributions p. 13; Corollary 1 p. 13; proof of Corollary 1 p. 30

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_costDomain
import Definitions.Def_InfoBargaining_SellerPayoff_sellerPayoffMaterial
import Definitions.Def_InfoBargaining_SellerPayoff_sellerPayoffOpportunity

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **Proposition 2: the seller's payoff rises in `θ_s` except for a fall at `1 − θ̃`; `U_s*`
falls in `c` except for a rise at `c_l`; `V_s*` rises in `c` except for a fall at `c_h`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
Proposition 2, p. 14: "Consider either of the four focal distributions. (i) The seller's
equilibrium expected payoff (U_s∗ or V_s∗) increases with its bargaining power θ_s, but may
decrease discontinuously at θ_s = 1 − θ̃; (ii) The seller's equilibrium expected payoff U_s∗
decreases with its material cost c, but may increase discontinuously at c = c_l; (iii) The
seller's equilibrium expected payoff V_s∗ increases with its opportunity cost c, but may
decrease discontinuously at c = c_h."
Here `U_s∗ = θ_s A(α∗, c)`, `V_s∗ = c + θ_s A(α∗, c)` (p. 12), the cost is linear (p. 13), and
`θ̃`, `c_l`, `c_h` are the thresholds of Corollary 1 (p. 13).

For every focal prior `P`:

1. for all `0 < α̲ < ᾱ < 1` and `k̄ > 0`:
   * (i) for every admissible `c` there is `θ̃ ∈ (0, 1]` with Corollary 1 (i)'s property
     (`α* = ᾱ` iff `θ̃ < θ_b = 1 − θ_s`), such that for `θ₁ < θ₂` in `(0, 1)`, a fall of `U_s*`
     or of `V_s*` from `θ₁` to `θ₂` forces `θ₁ < 1 − θ̃ ≤ θ₂`, and both payoffs are continuous
     in `θ_s` at every `θ ∈ (0, 1)` other than `1 − θ̃`;
   * (ii)–(iii) for every `θ_s ∈ (0, 1)` there are `c_l ≤ û ≤ c_h` with Corollary 1 (ii)'s
     property (`α* = ᾱ` iff `c_l < c < c_h`, for admissible `c`), such that for admissible
     `c₁ < c₂`, a rise of `U_s*` forces `c₁ ≤ c_l < c₂`, a fall of `V_s*` forces
     `c₁ < c_h ≤ c₂`, and both payoffs are continuous in `c` at every admissible `c ∉ {c_l, c_h}`;
2. ("may", (i)) some admissible parameters and `θ₁ < θ₂` make both `U_s*` and `V_s*` fall;
3. ("may", (ii)) some admissible parameters and costs `c₁ < c₂` make `U_s*` rise;
4. ("may", (iii)) some admissible parameters and costs `c₁ < c₂` make `V_s*` fall.

**Formalization Note.** `α*` is the least maximizer of (6) (Corollary 1's tie-break).
"Increases … but may decrease discontinuously at t₀" is read as: every decrease straddles
`t₀`, with the half-open sides fixed by that tie-break; continuity at every other point; and
for every focal prior an actual reversal for some admissible parameters. Monotonicity is weak
(strict is false: uniform prior, `c = 3/4`, `α̲ = 1/5` gives `U_s* ≡ 0` on a piece). The
thresholds are existential and pinned by Corollary 1's characterization of `α*`. The model is
encoded through the law of the posterior mean (`postMeanLaw`); the game is not formalized. -/
theorem proposition_2_seller_payoff_reversals (P : FocalPrior) :
    (∀ αl αh kbar : ℝ, 0 < αl → αl < αh → αh < 1 → 0 < kbar →
      -- (i): in θs, at each fixed c; θt is Corollary 1 (i)'s θ̃
      (∀ c ∈ P.costDomain, ∃ θt : ℝ, 0 < θt ∧ θt ≤ 1 ∧
        (∀ θs ∈ Set.Ioo (0:ℝ) 1,
          optimalInfo P.measure αl αh kbar (1 - θs) c = αh ↔ θt < 1 - θs) ∧
        (∀ θ₁ ∈ Set.Ioo (0:ℝ) 1, ∀ θ₂ ∈ Set.Ioo (0:ℝ) 1, θ₁ < θ₂ →
          (sellerPayoffMaterial P.measure αl αh kbar θ₂ c <
              sellerPayoffMaterial P.measure αl αh kbar θ₁ c →
            θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂) ∧
          (sellerPayoffOpportunity P.measure αl αh kbar θ₂ c <
              sellerPayoffOpportunity P.measure αl αh kbar θ₁ c →
            θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂)) ∧
        (∀ θ ∈ Set.Ioo (0:ℝ) 1, θ ≠ 1 - θt →
          ContinuousAt (fun θs => sellerPayoffMaterial P.measure αl αh kbar θs c) θ ∧
          ContinuousAt (fun θs => sellerPayoffOpportunity P.measure αl αh kbar θs c) θ)) ∧
      -- (ii) and (iii): in c, at each fixed θs; cl, ch are Corollary 1 (ii)'s thresholds
      (∀ θs ∈ Set.Ioo (0:ℝ) 1, ∃ cl ch : ℝ,
        cl ≤ priorMean P.measure ∧ priorMean P.measure ≤ ch ∧
        (∀ c ∈ P.costDomain,
          optimalInfo P.measure αl αh kbar (1 - θs) c = αh ↔ cl < c ∧ c < ch) ∧
        (∀ c₁ ∈ P.costDomain, ∀ c₂ ∈ P.costDomain, c₁ < c₂ →
          (sellerPayoffMaterial P.measure αl αh kbar θs c₁ <
              sellerPayoffMaterial P.measure αl αh kbar θs c₂ →
            c₁ ≤ cl ∧ cl < c₂) ∧
          (sellerPayoffOpportunity P.measure αl αh kbar θs c₂ <
              sellerPayoffOpportunity P.measure αl αh kbar θs c₁ →
            c₁ < ch ∧ ch ≤ c₂)) ∧
        (∀ c ∈ P.costDomain, c ≠ cl → c ≠ ch →
          ContinuousAt (fun x => sellerPayoffMaterial P.measure αl αh kbar θs x) c ∧
          ContinuousAt (fun x => sellerPayoffOpportunity P.measure αl αh kbar θs x) c))) ∧
    -- "may" in (i): a fall of both payoffs in θs
    (∃ αl αh kbar c θ₁ θ₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ c ∈ P.costDomain ∧
      0 < θ₁ ∧ θ₁ < θ₂ ∧ θ₂ < 1 ∧
      sellerPayoffMaterial P.measure αl αh kbar θ₂ c <
        sellerPayoffMaterial P.measure αl αh kbar θ₁ c ∧
      sellerPayoffOpportunity P.measure αl αh kbar θ₂ c <
        sellerPayoffOpportunity P.measure αl αh kbar θ₁ c) ∧
    -- "may" in (ii): a rise of U_s* in c
    (∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ P.costDomain ∧ c₂ ∈ P.costDomain ∧ c₁ < c₂ ∧
      sellerPayoffMaterial P.measure αl αh kbar θs c₁ <
        sellerPayoffMaterial P.measure αl αh kbar θs c₂) ∧
    -- "may" in (iii): a fall of V_s* in c
    (∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ P.costDomain ∧ c₂ ∈ P.costDomain ∧ c₁ < c₂ ∧
      sellerPayoffOpportunity P.measure αl αh kbar θs c₂ <
        sellerPayoffOpportunity P.measure αl αh kbar θs c₁) := by sorry

end InfoBargaining.SellerPayoff
