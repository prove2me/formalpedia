-- Prove2me | Theorems.Thm_InvRiskAlloc_proposition_7
-- name    : InvRiskAlloc.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:17.229091+00:00
-- url     : https://prove2.me/theorems/b213d59c-3efe-4d52-a517-6ea2bacf47b6
-- title:
--   Proposition 7, p. 20 — the optimal consignment contract is $(q^{NW}_1,\rho_{\beta_1}(\Psi))$
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mu)$ is a probability space carrying the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity; $s$ is the selling price and $c$ the unit cost with $0<c<s$; $0<\beta_2<\beta_1\le 1$ are the two possible risk attitudes and $\nu\in(0,1)$ is the prior probability of $\beta_1$. Demand is nonnegative, its distribution function $F_D$ is continuous and strictly increasing on $[0,\infty)$, and $F_D^{-1}$ is its quantile; $\Psi\ge 0$ and $\rho_{\beta_1}(\Psi)$ is finite. $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ is the $\beta$-CVaR, $S_\beta(q)=\rho_\beta(\min\{q,D\})$, $\Delta S=S_{\beta_1}-S_{\beta_2}$, $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$, and $\hat q^*_\beta=q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$.
--
--   Under the consignment contract the manufacturer solves Problem C: maximize $sS_1(q)-cq-t$ over $q\ge0$ and $t\in\mathbb R$ subject to $t\ge\rho_{\beta_i}(\Psi)$ for $i=1,2$. Its optimal solution is
--   $$(\tilde q^C,\tilde t^C)=\big(q^{NW}_1,\ \rho_{\beta_1}(\Psi)\big),$$
--   and it is the only optimal solution.
--
--   The consignment quantity is the risk-neutral newsvendor quantity, whatever the retailer's type and outside opportunity; it is the right-hand side of the comparison in Proposition 9.
--
--   Differences from the source:
--
--   - reading: D is supported on [0,∞) (p. 8) → the support is all of [0,∞): F_D strictly increasing on [0,∞); reason: with a gap in the support η(β2) need not exist (D uniform on [0,1]∪[2,3], s = 1, c = 1/2, ν = 1/2, β2 = 1/2: the left side of η’s equation jumps from 0.75 to 1.25 at η′ = 1, past the right side 1); the weaker reading D ≥ 0 makes §4.3.1 false
--   - generalization: D has distribution F_D and density f_D (p. 8) → D measurable, D ≥ 0 a.s., F_D continuous and strictly increasing on [0,∞); no density; reason: a full-support law with a density satisfies these hypotheses, so the source’s setting is a special case
--   - encoding: c < s (p. 8) → 0 < c < s; reason: at c = 0 the first-best quantity F_D^{-1}(1) and the interval [1, s/(s−c)] are undefined; the case is excluded, not a valid instance
--   - encoding: Ψ ≥ 0 and ρ_β(Ψ) a real number (pp. 8, 12) → Ψ measurable, Ψ ≥ 0 a.s., and β1 < 1 or Ψ integrable; reason: for Ψ ≥ 0 and β < 1 the CVaR is finite; at β1 = 1 it is E[Ψ], so the disjunction excludes only ρ_β1(Ψ) = +∞, which the real-valued IR constraints already exclude
--   - reading: the optimal consignment contract is (q̃^C, t̃^C) → it is an optimal solution of C and every optimal solution equals it; reason: the stronger reading of "the optimal contract"
--   - encoding: C, (4), maximizes over q, t without q ≥ 0 → q ≥ 0; reason: q is an order quantity; the complete-information problem of §3.2.2 states q ≥ 0
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), Proposition 7, p. 20; Problem C, eqs. (4)–(5), p. 19

import Mathlib
import Definitions.Def_InvRiskAlloc_Model

open MeasureTheory

namespace InvRiskAlloc

/-- Proposition 7, p. 20 (Hou–Lu, SSRN 4297536, accepted manuscript of MSOM 2024,
doi:10.1287/msom.2022.0624): the optimal consignment contract is
`(q̃^C, t̃^C) = (q^NW_1, ρ_{β₁}(Ψ))`, i.e. this contract is an optimal solution of Problem C,
(4)–(5) p. 19, and the only one. -/
theorem proposition_7 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Standing) :
    M.IsOptC (M.qNW 1, RiskPostpone.Threshold.cvar M.μ M.β₁ M.Ψ) ∧
      ∀ y : ℝ × ℝ, M.IsOptC y → y = (M.qNW 1, RiskPostpone.Threshold.cvar M.μ M.β₁ M.Ψ) := by sorry

end InvRiskAlloc
