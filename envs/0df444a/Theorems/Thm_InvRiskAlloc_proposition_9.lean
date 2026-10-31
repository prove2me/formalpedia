-- Prove2me | Theorems.Thm_InvRiskAlloc_proposition_9
-- name    : InvRiskAlloc.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:25.255077+00:00
-- url     : https://prove2.me/theorems/5682485f-2fc7-4cb3-8185-e6a2c97a5971
-- title:
--   Proposition 9, p. 21 — pre-order out-orders consignment iff (1)–(3) (corrected: condition 1’s second bound is $\beta_2/(1-\nu+\nu\beta_2/\eta(\beta_2))$)
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mu)$ is a probability space carrying the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity; $s$ is the selling price and $c$ the unit cost with $0<c<s$; $0<\beta_2<\beta_1\le 1$ are the two possible risk attitudes and $\nu\in(0,1)$ is the prior probability of $\beta_1$. Demand is nonnegative, its distribution function $F_D$ is continuous and strictly increasing on $[0,\infty)$, and $F_D^{-1}$ is its quantile; $\Psi\ge 0$ and $\rho_{\beta_1}(\Psi)$ is finite. $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ is the $\beta$-CVaR, $S_\beta(q)=\rho_\beta(\min\{q,D\})$, $\Delta S=S_{\beta_1}-S_{\beta_2}$, $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$, and $\hat q^*_\beta=q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$.
--
--   Let $\eta=\eta(\beta_2)$ be the threshold of §4.3.1. Under the pre-order contract the manufacturer chooses the option $P\in\{P(1,2),P(1),P(2)\}$ with the highest optimal value (ties go to P(1,2), and P(1) beats P(2) on a tie) and trades iff that value is nonnegative; the expected order quantity is $\nu q_1+(1-\nu)q_2$, $\nu q_1$ or $(1-\nu)q_2$ for an optimal solution of the chosen problem, and $0$ without trade. Under the consignment contract the order quantity $\tilde q$ is that of an optimal solution of Problem C.
--
--   Then such optimal solutions exist, and for every one of them the expected order quantity under the pre-order contract is strictly higher than $\tilde q$ if and only if
--
--   1. the risk attitudes are dispersed enough:
--   $$\beta_1>\max\Big\{\frac{\eta(s-c)}{s-\nu c},\ \frac{\beta_2}{1-\nu+\nu\beta_2/\eta}\Big\};$$
--   2. the outside opportunity is risky enough: $\Delta\rho(\Psi)>s\Delta S\big(F_D^{-1}(\eta(1-c/s))\big)$;
--   3. the manufacturer trades with both types: $P=P(1,2)$ and its optimal value is nonnegative.
--
--   This is the paper's main result: pushing the inventory risk to a risk-averse retailer can raise the expected order, because screening the retailer's private risk attitude distorts the less risk-averse type's quantity upward.
--
--   **Correction.** The paper prints the second bound of condition 1 as $\beta_2/(1-\nu+\eta\nu\beta_2)$. That version is false: take $s=1$, $c=0.5$, $\nu=0.3$, $\beta_2=0.8$, $\beta_1=0.8555$, $D$ exponential with mean $10$, and $\Psi=0$ with probability $0.8$ and $6.165766$ with probability $0.2$ (so $\rho_{\beta_2}(\Psi)=0$, $\rho_{\beta_1}(\Psi)=0.4$). Then $\eta=1.346503$, the printed bounds are $0.792060$ and $0.781891<\beta_1$, condition 2 holds ($0.4>0.361117$) and $P=P(1,2)$ with value $0.890531\ge0$, yet the expected order $0.3\cdot7.140959+0.7\cdot5.108256=5.718067$ is below $q^{NW}_1=6.931472$. The bound $\beta_2/(1-\nu+\nu\beta_2/\eta)=0.910913$ is the one the high-risk threshold $\hat\beta_1>\eta$ of Proposition 4 produces.
--
--   Differences from the source:
--
--   - reading: D is supported on [0,∞) (p. 8) → the support is all of [0,∞): F_D strictly increasing on [0,∞); reason: with a gap in the support η(β2) need not exist (D uniform on [0,1]∪[2,3], s = 1, c = 1/2, ν = 1/2, β2 = 1/2: the left side of η’s equation jumps from 0.75 to 1.25 at η′ = 1, past the right side 1); the weaker reading D ≥ 0 makes §4.3.1 false
--   - generalization: D has distribution F_D and density f_D (p. 8) → D measurable, D ≥ 0 a.s., F_D continuous and strictly increasing on [0,∞); no density; reason: a full-support law with a density satisfies these hypotheses, so the source’s setting is a special case
--   - encoding: c < s (p. 8) → 0 < c < s; reason: at c = 0 the first-best quantity F_D^{-1}(1) and the interval [1, s/(s−c)] are undefined; the case is excluded, not a valid instance
--   - encoding: Ψ ≥ 0 and ρ_β(Ψ) a real number (pp. 8, 12) → Ψ measurable, Ψ ≥ 0 a.s., and β1 < 1 or Ψ integrable; reason: for Ψ ≥ 0 and β < 1 the CVaR is finite; at β1 = 1 it is E[Ψ], so the disjunction excludes only ρ_β1(Ψ) = +∞, which the real-valued IR constraints already exclude
--   - correction: β1 > max{η(β2)(s−c)/(s−νc), β2/(1−ν+η(β2)νβ2)} → β1 > max{η(s−c)/(s−νc), β2/(1−ν+νβ2/η)}; reason: printed version false: s = 1, c = 0.5, ν = 0.3, β2 = 0.8, β1 = 0.8555, D ~ Exp(mean 10), Ψ = 0 w.p. 0.8 and 6.165766 w.p. 0.2 satisfy printed conditions 1–3 (η = 1.346503, bounds 0.792060 and 0.781891, Δρ = 0.4 > 0.361117, P = P(1,2) with value 0.890531), yet the expected order 5.718067 < q^NW_1 = 6.931472; the corrected bound is 0.910913 > β1
--   - reading: the expected order quantity under the pre-order contract → νq1 + (1−ν)q2, νq1 or (1−ν)q2 for an optimal solution of the chosen option, 0 if the manufacturer does not trade; reason: an unserved type orders nothing; η’s equation (p. 20) is exactly this expectation under P(1,2)
--   - reading: the expected order quantity under the consignment contract → the q of an optimal solution of Problem C, regardless of Proposition 8’s trading condition; reason: η’s equation compares with F_D^{-1}(1 − c/s) unconditionally and Proposition 9 states no consignment condition
--   - reading: P is the option with the highest profit (p. 14) → attained optimal values; an infeasible option does not compete; ties with P(1,2) go to P(1,2), a P(1)–P(2) tie goes to P(1); reason: Propositions 3 and 6 send ties to P(1,2); without the rule the medium-to-high regime has a tie that breaks the iff
--   - reading: the manufacturer trades with both types (condition 3; exact condition in Proposition EC.1, not in this artifact) → P = P(1,2) and its optimal value is ≥ 0; reason: §3.2.1, p. 8: the manufacturer offers a contract iff her optimal profit is ≥ 0
--   - reading: the expected order quantities (one menu each) → existence of optimal solutions is asserted and the iff holds for every optimal solution of the chosen problem and of C; reason: makes the comparison independent of how an optimal solution is picked and rules out a vacuous statement
--   - encoding: η(β2) ∈ [1, s/(s−c)] → any η with 1 ≤ η < s/(s−c) solving η’s equation (unique by §4.3.1); reason: F_D^{-1}(1) at the right endpoint is not a real number
--   - encoding: P(1) and P(2), (2)–(3), maximize over q, U without q ≥ 0 → q ≥ 0 in P(1) and P(2); reason: q is an order quantity; (1) and §3.2.1 state q ≥ 0
--   - encoding: C, (4), maximizes over q, t without q ≥ 0 → q ≥ 0; reason: q is an order quantity; the complete-information problem of §3.2.2 states q ≥ 0
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), Proposition 9, p. 21; η(β2) from §4.3.1, p. 20

import Mathlib
import Definitions.Def_InvRiskAlloc_Model

open MeasureTheory

namespace InvRiskAlloc

/-- Proposition 9, p. 21 (Hou–Lu, SSRN 4297536, accepted manuscript of MSOM 2024,
doi:10.1287/msom.2022.0624), with the second bound of condition 1 corrected. Let `η = η(β₂)`
(§4.3.1, p. 20). The expected order quantity under the pre-order contract is strictly higher
than the order quantity under the consignment contract if and only if

1. `β₁ > max{η(s − c)/(s − νc), β₂/(1 − ν + νβ₂/η)}`,
2. `Δρ(Ψ) > sΔS(F_D⁻¹(η(1 − c/s)))`, and
3. the manufacturer trades with both types under the pre-order contract: the chosen option is
   `P = P(1,2)` and its optimal value is `≥ 0`.

The statement also asserts that the pre-order expected quantity and an optimal consignment
contract exist, and the equivalence holds for every optimal solution of the chosen pre-order
problem and every optimal solution `(q̃, t̃)` of Problem C.

**Formalization Note** The paper prints the second bound of condition 1 as
`β₂/(1 − ν + η(β₂)νβ₂)`; that condition is false (see the item's natural-language statement for
a counterexample). The option choice (`Model.Chooses`), the trading rule and the expected order
quantity (`Model.IsPreOrderExpectedQty`) follow pp. 8, 14 and 20. -/
theorem proposition_9 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Standing)
    (η : ℝ) (hη : M.IsEta η) :
    (∃ Q, M.IsPreOrderExpectedQty Q) ∧ (∃ y, M.IsOptC y) ∧
      ∀ Q, M.IsPreOrderExpectedQty Q → ∀ y, M.IsOptC y →
        (y.1 < Q ↔
          (max (η * (M.s - M.c) / (M.s - M.ν * M.c)) (M.β₂ / (1 - M.ν + M.ν * M.β₂ / η)) <
              M.β₁ ∧
            M.s * M.ΔS (M.Finv (η * (1 - M.c / M.s))) < M.Δρ ∧
            ∃ v, M.Chooses .P12 v ∧ 0 ≤ v)) := by sorry

end InvRiskAlloc
