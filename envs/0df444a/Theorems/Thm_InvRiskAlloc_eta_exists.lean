-- Prove2me | Theorems.Thm_InvRiskAlloc_eta_exists
-- name    : InvRiskAlloc.eta_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:14.258347+00:00
-- url     : https://prove2.me/theorems/15a5c452-4849-485d-af15-24af69444d57
-- title:
--   §4.3.1, p. 20 — the threshold $\eta(\beta_2)$ exists, is unique and exceeds 1
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mu)$ is a probability space carrying the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity; $s$ is the selling price and $c$ the unit cost with $0<c<s$; $0<\beta_2<\beta_1\le 1$ are the two possible risk attitudes and $\nu\in(0,1)$ is the prior probability of $\beta_1$. Demand is nonnegative, its distribution function $F_D$ is continuous and strictly increasing on $[0,\infty)$, and $F_D^{-1}$ is its quantile; $\Psi\ge 0$ and $\rho_{\beta_1}(\Psi)$ is finite. $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ is the $\beta$-CVaR, $S_\beta(q)=\rho_\beta(\min\{q,D\})$, $\Delta S=S_{\beta_1}-S_{\beta_2}$, $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$, and $\hat q^*_\beta=q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$.
--
--   There is exactly one $\eta\in[1,s/(s-c))$ with
--   $$\nu F_D^{-1}\big(\eta(1-c/s)\big)+(1-\nu)F_D^{-1}\big(\beta_2(1-c/s)\big)=F_D^{-1}(1-c/s),$$
--   and this $\eta=\eta(\beta_2)$ satisfies $\eta>1$.
--
--   The left side is the expected pre-order quantity when the less risk-averse type orders as a firm with virtual risk attitude $\eta$ and the other type orders first-best; $\eta(\beta_2)$ is the virtual risk attitude at which it matches the consignment quantity, and it enters both conditions of Proposition 9.
--
--   Differences from the source:
--
--   - reading: D is supported on [0,∞) (p. 8) → the support is all of [0,∞): F_D strictly increasing on [0,∞); reason: with a gap in the support η(β2) need not exist (D uniform on [0,1]∪[2,3], s = 1, c = 1/2, ν = 1/2, β2 = 1/2: the left side of η’s equation jumps from 0.75 to 1.25 at η′ = 1, past the right side 1); the weaker reading D ≥ 0 makes §4.3.1 false
--   - generalization: D has distribution F_D and density f_D (p. 8) → D measurable, D ≥ 0 a.s., F_D continuous and strictly increasing on [0,∞); no density; reason: a full-support law with a density satisfies these hypotheses, so the source’s setting is a special case
--   - encoding: c < s (p. 8) → 0 < c < s; reason: at c = 0 the first-best quantity F_D^{-1}(1) and the interval [1, s/(s−c)] are undefined; the case is excluded, not a valid instance
--   - encoding: Ψ ≥ 0 and ρ_β(Ψ) a real number (pp. 8, 12) → Ψ measurable, Ψ ≥ 0 a.s., and β1 < 1 or Ψ integrable; reason: for Ψ ≥ 0 and β < 1 the CVaR is finite; at β1 = 1 it is E[Ψ], so the disjunction excludes only ρ_β1(Ψ) = +∞, which the real-valued IR constraints already exclude
--   - reading: η(β2) = {η′ ∈ [1, s/(s−c)] | …}, "whose existence can be easily verified" → exactly one η satisfies the equation; reason: the paper uses the set as a number, η(β2); uniqueness is what makes that well defined
--   - generalization: existence of η(β2) → existence, uniqueness and η > 1; reason: the Lean conclusion contains the source’s existence claim
--   - encoding: η′ ∈ [1, s/(s−c)] → 1 ≤ η < s/(s−c); reason: at η′ = s/(s−c) the quantile F_D^{-1}(1) is not a real number, so the endpoint is no instance
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), §4.3.1, p. 20, display defining η(β2)

import Mathlib
import Definitions.Def_InvRiskAlloc_Model

open MeasureTheory

namespace InvRiskAlloc

/-- §4.3.1, p. 20 (Hou–Lu, SSRN 4297536, accepted manuscript of MSOM 2024,
doi:10.1287/msom.2022.0624): the threshold `η(β₂)` exists. There is exactly one
`η ∈ [1, s/(s − c))` with `νF_D⁻¹(η(1 − c/s)) + (1 − ν)F_D⁻¹(β₂(1 − c/s)) = F_D⁻¹(1 − c/s)`,
and it satisfies `η > 1`.

**Formalization Note** Uniqueness is what makes the paper's notation `η(β₂)` a function; the
interval is half-open because `F_D⁻¹(1)` is not a real number (`Model.IsEta`). -/
theorem eta_exists {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Standing) :
    ∃ η : ℝ, M.IsEta η ∧ 1 < η ∧ ∀ η' : ℝ, M.IsEta η' → η' = η := by sorry

end InvRiskAlloc
