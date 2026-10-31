-- Prove2me | Theorems.Thm_InvRiskAlloc_first_best_quantity
-- name    : InvRiskAlloc.first_best_quantity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:12.391449+00:00
-- url     : https://prove2.me/theorems/9a7810c5-0e5a-49d2-9f71-d7f051cc7842
-- title:
--   §3.1, p. 8 — the CVaR first-best order quantity $q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mu)$ is a probability space carrying the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity; $s$ is the selling price and $c$ the unit cost with $0<c<s$; $0<\beta_2<\beta_1\le 1$ are the two possible risk attitudes and $\nu\in(0,1)$ is the prior probability of $\beta_1$. Demand is nonnegative, its distribution function $F_D$ is continuous and strictly increasing on $[0,\infty)$, and $F_D^{-1}$ is its quantile; $\Psi\ge 0$ and $\rho_{\beta_1}(\Psi)$ is finite. $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ is the $\beta$-CVaR, $S_\beta(q)=\rho_\beta(\min\{q,D\})$, $\Delta S=S_{\beta_1}-S_{\beta_2}$, $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$, and $\hat q^*_\beta=q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$.
--
--   For every risk attitude $\beta\in(0,1]$, the order quantity $q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$ maximizes the CVaR of the system-wide profit $\phi(q)=s\min\{q,D\}-cq$, and it is the only maximizer:
--   $$q^{NW}_\beta=\arg\max_{q\in\mathbb R}\ \rho_\beta(\phi(q)),\qquad \rho_\beta(\phi(q))=sS_\beta(q)-cq.$$
--
--   With $\beta=1$ this is the risk-neutral newsvendor quantity $q^{NW}_1=F_D^{-1}(1-c/s)$, and with $\beta=\beta_i$ it is the complete-information pre-order quantity $\hat q^*_{\beta_i}$ (§3.2.1). Every optimal menu of the mission is expressed through these quantities.
--
--   Differences from the source:
--
--   - reading: D is supported on [0,∞) (p. 8) → the support is all of [0,∞): F_D strictly increasing on [0,∞); reason: with a gap in the support η(β2) need not exist (D uniform on [0,1]∪[2,3], s = 1, c = 1/2, ν = 1/2, β2 = 1/2: the left side of η’s equation jumps from 0.75 to 1.25 at η′ = 1, past the right side 1); the weaker reading D ≥ 0 makes §4.3.1 false
--   - generalization: D has distribution F_D and density f_D (p. 8) → D measurable, D ≥ 0 a.s., F_D continuous and strictly increasing on [0,∞); no density; reason: a full-support law with a density satisfies these hypotheses, so the source’s setting is a special case
--   - encoding: c < s (p. 8) → 0 < c < s; reason: at c = 0 the first-best quantity F_D^{-1}(1) and the interval [1, s/(s−c)] are undefined; the case is excluded, not a valid instance
--   - encoding: Ψ ≥ 0 and ρ_β(Ψ) a real number (pp. 8, 12) → Ψ measurable, Ψ ≥ 0 a.s., and β1 < 1 or Ψ integrable; reason: for Ψ ≥ 0 and β < 1 the CVaR is finite; at β1 = 1 it is E[Ψ], so the disjunction excludes only ρ_β1(Ψ) = +∞, which the real-valued IR constraints already exclude
--   - encoding: ρ_β(ϕ(q)) (p. 8) → s·S_β(q) − c·q; reason: the paper defines ρ_β(ϕ(q)) this way on p. 8; Lean uses that definition rather than the CVaR of ϕ(q)
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), §3.1, p. 8, display defining q^NW_β

import Mathlib
import Definitions.Def_InvRiskAlloc_Model

open MeasureTheory

namespace InvRiskAlloc

/-- §3.1, p. 8 (Hou–Lu, SSRN 4297536, accepted manuscript of MSOM 2024,
doi:10.1287/msom.2022.0624): for every risk attitude `β ∈ (0, 1]` the first-best order quantity
`q^NW_β = F_D⁻¹(β(1 − c/s))` is the unique maximizer over `q ∈ ℝ` of the CVaR of the
system-wide profit `ρ_β(ϕ(q)) = sS_β(q) − cq`.

**Formalization Note** `ρ_β(ϕ(q))` is the paper's own definition `sS_β(q) − cq`
(`Model.rhoPhi`). The paper's `arg max_q` carries no sign restriction, so the maximum is taken
over all real `q`. -/
theorem first_best_quantity {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Standing)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∀ q : ℝ, M.rhoPhi β q ≤ M.rhoPhi β (M.qNW β)) ∧
      ∀ q : ℝ, M.rhoPhi β q = M.rhoPhi β (M.qNW β) → q = M.qNW β := by sorry

end InvRiskAlloc
