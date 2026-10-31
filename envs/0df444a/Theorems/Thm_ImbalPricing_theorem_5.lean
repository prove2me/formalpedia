-- Prove2me | Theorems.Thm_ImbalPricing_theorem_5
-- name    : ImbalPricing.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:44.495979+00:00
-- url     : https://prove2.me/theorems/23282b19-b165-44cd-a5bb-c4fe18927312
-- title:
--   Theorem 5 (corrected: equilibrium, not unique; formula needs $\sum_i\gamma^i\mathrm{Cov}(\epsilon,\nu^i)=0$): optimal pricing makes full commitment an equilibrium with minimum expected deadweight loss
-- statement:
--   Consider the two-stage electricity market of the paper: $N\ge1$ strategic low-cost generators (LCGs) with expected productions $\gamma^i>0$ and market share $\gamma=\sum_i\gamma^i\le1$; a high-cost generator with marginal-cost slopes $\alpha_2\ge\alpha_1\ge0$; mean-zero, square-integrable, arbitrarily correlated forecast errors $\epsilon$ (demand) and $\nu^1,\dots,\nu^N$ (LCG productions) on a probability space. LCG $i$ chooses its offer adjustment $d^i\in[-1,1/\gamma-1]$ to maximize its expected profit $\Pi^i_{op}$ under the optimal imbalance price $p^i_{2,op}=p_1+\alpha_2H_2-\alpha_1L_1^i$ (Definition 4). Then:
--
--   1. **Competitive behavior.** Full commitment, $d=0$, is a Nash equilibrium of the offer game.
--   2. **Strictness.** If $\alpha_1<\alpha_2$, then for every LCG $i$, offering $d^i=0$ is its unique best response in $[-1,1/\gamma-1]$ when all other LCGs offer $0$: $\Pi^i_{op}(x,0_{-i})<\Pi^i_{op}(0)$ for every $x\ne0$ in the box.
--   3. **Full efficiency in a deterministic setting.** If $\epsilon=0$ and $\nu^i=0$ almost surely for every $i$, then $DWL=0$ almost surely at $d=0$.
--   4. **Expected deadweight loss.** If $\sum_{i=1}^N\gamma^i\,\mathrm{Cov}(\epsilon,\nu^i)=0$ (in particular if $\mathrm{Cov}(\epsilon,\nu^i)=0$ for every $i$), then at $d=0$
--   $$\mathbb E[DWL_{op}]=\frac12(\alpha_2-\alpha_1)\Big(\mathrm{Var}(\epsilon)+\sum_{j=1}^N\sum_{i=1}^N\gamma^j\gamma^i\,\mathrm{Cov}(\nu^j,\nu^i)\Big).$$
--   5. **Maximum efficiency.** $\mathbb E[DWL]$ at $d=0$ is at most $\mathbb E[DWL]$ at every offer profile $d$.
--
--   The theorem shows that an imbalance price can be designed so that strategic renewable generators have no incentive to under-commit, and the only remaining deadweight loss is the one caused by forecast errors.
--
--   Differences from the source:
--
--   - correction: any LCG i behaves as if in a perfect competition setting, choosing dⁱ = 0 (read as: d = 0 is the unique equilibrium, or every equilibrium is efficient) → d = 0 is a Nash equilibrium (clause 1) and, when α₁ < α₂, 0 is each LCG's unique best response to the others' 0 (clause 2); reason: uniqueness is false: at α₁ = α₂ every own offer is a best response to the others' 0; at N = 2, γ = (1/4, 1/4), α₁ = 1, α₂ = 2, ε = ν = 0 the profile (1/2, −1/2) is an equilibrium; at γ = (1/10, 1/10), α₁ = 1, α₂ = 3/2, ε = ν = 0 the equilibrium (−1, 3/2) has DWL = 1/1600 > 0
--   - correction: E[DWL_op] = 1/2(α₂ − α₁)(Var(ɛ) + ΣⱼΣᵢγʲγⁱCov(νʲ, νⁱ)) with no condition on ε and νⁱ → the formula is stated under Σᵢγⁱ Cov(ε, νⁱ) = 0 (clause 4); reason: at d = 0 the formula drops −2E[εL₂] = −2Σᵢγⁱ Cov(ε, νⁱ), so this condition is exactly what it needs; N = 1, γ¹ = 1/2, α₁ = 1, α₂ = 3, ε = ν¹ = ±1/2 with probability 1/2 each gives E[DWL] = 1/16 at d = 0, while the formula gives 5/16
--   - reading: maximum economic efficiency in a probabilistic setting → E[DWL] at d = 0 ≤ E[DWL] at every offer profile d (clause 5); reason: the text after Eq. (6), p.8, and after Theorem 5, p.13, says the remaining DWL is the forecast-error part, which no offer removes
--   - reading: full economic efficiency in a deterministic setting (i.e., DWL = 0) → if ε = 0 and every νⁱ = 0 almost surely, then DWL = 0 almost surely at d = 0 (clause 3); reason: 'deterministic' means no forecast error; random variables are determined only up to null sets
--   - reading: profit Πⁱ = p₁L₁ⁱ + p₂ⁱL₂ⁱ (Eq. (9) prints no expectation; Eq. (20) prints p₁L₁ⁱ + E[p₂ⁱL₂ⁱ]) → expected profit Πⁱ_op = E[p₁L₁ⁱ + p^i_{2,op}L₂ⁱ]; reason: the offer is chosen in Stage 1 before ε, ν are realized, Eq. (20) and Proposition 1 take the expectation, and p₁, L₁ⁱ are deterministic, so both printed forms agree with this one
--   - reading: LCGs choose dⁱ ∈ [−1, (1/γ) − 1] after a private signal γⁱ (p.7) → pure Nash equilibrium of the complete-information game over offers in [−1, 1/γ − 1]; reason: all γⁱ enter the strategy set through γ = Σγⁱ and enter Theorem 1's equilibrium (10), so they are common knowledge
--   - reading: MC₂ 'continues only until the point where MC₂ reaches zero' (p.6) → prices and costs linear as in Eqs. (1)–(4), (8), (26), with no floor at zero; reason: every display and result of the paper uses the linear forms
--   - generalization: ε and νⁱ unbiased and bounded with ε ≥ −1, νⁱ ≥ −1 (pp.5–6) → ε and νⁱ have mean 0 and finite second moment (MemLp 2), with no bound; reason: the bounds only keep realized demand and production nonnegative and enter no formula; every bounded random variable is square integrable, so the source's case is included
--   - reading: expected productions γⁱ of N ≥ 1 LCGs with γ = Σγⁱ ≤ 1 (pp.5–6) → 0 < N, γⁱ > 0 for every i, Σγⁱ ≤ 1; reason: γⁱ is an expected production share and Eq. (10) divides by γⁱ, so γⁱ > 0 is part of the model
--   - generalization: maximum efficiency compared with offer profiles in the box → clause 5 for every real offer profile d; reason: E[DWL] at d = 0 is minimal over all real profiles; the box is a special case
--   - encoding: E[·], VAR(ɛ), Cov(νʲ, νⁱ) of random variables; LCGs i = 1, …, N → Bochner integrals against a probability measure μ, Mathlib's variance and covariance; LCGs indexed by Fin N; reason: Lean convention; under MemLp 2 these are the usual moments, same instances
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §7, Theorem 5, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ImbalPricing_Market
import Definitions.Def_ImbalPricing_OPMechanism
import Definitions.Def_ImbalPricing_ExpectedDWL

open MeasureTheory ProbabilityTheory

namespace ImbalPricing

/-- **Theorem 5** (corrected: equilibrium, not unique; formula needs `∑ γⁱ Cov(ε, νⁱ) = 0`),
Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal Electricity Imbalance Pricing for the
Emerging Penetration of Renewable and Low-Cost Generators*, MSOM Articles in Advance (2023), §7,
p.13 (PDF p.15). Under the standing assumptions of §3.1 and the OP mechanism (Definition 4):

1. full commitment `d = 0` is a Nash equilibrium of the offer game;
2. if `α₁ < α₂`, then `dⁱ = 0` is LCG `i`'s unique best response in `[−1, 1/γ − 1]` when all
   others offer `0`;
3. in a deterministic setting (`ε = 0` and every `νⁱ = 0` almost surely), `DWL = 0` almost
   surely at `d = 0`;
4. if `∑_i γⁱ Cov(ε, νⁱ) = 0` (e.g. `ε` uncorrelated with every `νⁱ`), then
   `E[DWL_op] = ½ (α₂ − α₁) (Var(ε) + ∑_j ∑_i γʲγⁱ Cov(νʲ, νⁱ))` at `d = 0`;
5. this is the maximum economic efficiency: `E[DWL]` at `d = 0` is at most `E[DWL]` at every
   offer profile.

**Formalization Note.** "Any LCG `i` … choosing `dⁱ = 0`" cannot mean that `d = 0` is the
unique equilibrium: at `α₁ = 1`, `α₂ = 2`, `γ = (1/4, 1/4)`, `ε = ν = 0`, the profile
`(1/2, −1/2)` is also an equilibrium, and at `α₁ = 1`, `α₂ = 3/2`, `γ = (1/10, 1/10)` the
equilibrium `(−1, 3/2)` has `DWL = 1/1600 > 0`. Clause 4 needs `∑_i γⁱ Cov(ε, νⁱ) = 0` (see Lemma 1).
Profits are expected profits; expectations are Bochner integrals. -/
theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Market Ω N) (hM : M.Standing) :
    M.IsNashOP 0 ∧
      (M.α₁ < M.α₂ → ∀ i, ∀ x ∈ M.offerBox, x ≠ 0 →
        M.profitOP (Function.update (0 : Fin N → ℝ) i x) i < M.profitOP 0 i) ∧
      (M.ε =ᵐ[M.μ] 0 → (∀ i, M.ν i =ᵐ[M.μ] 0) → ∀ᵐ ω ∂M.μ, M.DWL 0 ω = 0) ∧
      ((∑ i, M.γ i * covariance M.ε (M.ν i) M.μ = 0) →
        M.expectedDWL 0 =
          (M.α₂ - M.α₁) / 2 *
            (variance M.ε M.μ + ∑ j, ∑ i, M.γ j * M.γ i * covariance (M.ν j) (M.ν i) M.μ)) ∧
      (∀ d : Fin N → ℝ, M.expectedDWL 0 ≤ M.expectedDWL d) := by sorry

end ImbalPricing
