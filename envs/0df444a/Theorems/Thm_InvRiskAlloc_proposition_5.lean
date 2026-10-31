-- Prove2me | Theorems.Thm_InvRiskAlloc_proposition_5
-- name    : InvRiskAlloc.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:07.356211+00:00
-- url     : https://prove2.me/theorems/1c39dc5d-c861-492f-b3fa-ae546caaa3ad
-- title:
--   Proposition 5, p. 16 (Table 4) — medium outside risk: first-best menus under every option
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mu)$ is a probability space carrying the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity; $s$ is the selling price and $c$ the unit cost with $0<c<s$; $0<\beta_2<\beta_1\le 1$ are the two possible risk attitudes and $\nu\in(0,1)$ is the prior probability of $\beta_1$. Demand is nonnegative, its distribution function $F_D$ is continuous and strictly increasing on $[0,\infty)$, and $F_D^{-1}$ is its quantile; $\Psi\ge 0$ and $\rho_{\beta_1}(\Psi)$ is finite. $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ is the $\beta$-CVaR, $S_\beta(q)=\rho_\beta(\min\{q,D\})$, $\Delta S=S_{\beta_1}-S_{\beta_2}$, $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$, and $\hat q^*_\beta=q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$.
--
--   Suppose $s\Delta S(\hat q^*_{\beta_2})\le\Delta\rho(\Psi)\le s\Delta S(\hat q^*_{\beta_1})$. Then the optimal pre-order contract menus are those of Table 4, each the unique optimal solution of its problem:
--
--   1. P(1,2): $(q_1,U_1)=(\hat q^*_{\beta_1},\rho_{\beta_1}(\Psi))$ and $(q_2,U_2)=(\hat q^*_{\beta_2},\rho_{\beta_2}(\Psi))$;
--   2. P(1): $(q_1,U_1)=(\hat q^*_{\beta_1},\rho_{\beta_1}(\Psi))$;
--   3. P(2): $(q_2,U_2)=(\hat q^*_{\beta_2},\rho_{\beta_2}(\Psi))$.
--
--   In the medium range neither type wants to mimic the other, so the manufacturer achieves the complete-information outcome whatever she trades.
--
--   Differences from the source:
--
--   - reading: D is supported on [0,∞) (p. 8) → the support is all of [0,∞): F_D strictly increasing on [0,∞); reason: with a gap in the support η(β2) need not exist (D uniform on [0,1]∪[2,3], s = 1, c = 1/2, ν = 1/2, β2 = 1/2: the left side of η’s equation jumps from 0.75 to 1.25 at η′ = 1, past the right side 1); the weaker reading D ≥ 0 makes §4.3.1 false
--   - generalization: D has distribution F_D and density f_D (p. 8) → D measurable, D ≥ 0 a.s., F_D continuous and strictly increasing on [0,∞); no density; reason: a full-support law with a density satisfies these hypotheses, so the source’s setting is a special case
--   - encoding: c < s (p. 8) → 0 < c < s; reason: at c = 0 the first-best quantity F_D^{-1}(1) and the interval [1, s/(s−c)] are undefined; the case is excluded, not a valid instance
--   - encoding: Ψ ≥ 0 and ρ_β(Ψ) a real number (pp. 8, 12) → Ψ measurable, Ψ ≥ 0 a.s., and β1 < 1 or Ψ integrable; reason: for Ψ ≥ 0 and β < 1 the CVaR is finite; at β1 = 1 it is E[Ψ], so the disjunction excludes only ρ_β1(Ψ) = +∞, which the real-valued IR constraints already exclude
--   - reading: the optimal pre-order contract menu is given in Table k → each table entry is an optimal solution and every optimal solution equals it; reason: the stronger reading of "the optimal menu"; the numerical checks of the planning session found no ties
--   - encoding: P(1) and P(2), (2)–(3), maximize over q, U without q ≥ 0 → q ≥ 0 in P(1) and P(2); reason: q is an order quantity; (1) and §3.2.1 state q ≥ 0
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), Proposition 5, p. 16, and Table 4, p. 17

import Mathlib
import Definitions.Def_InvRiskAlloc_Model

open MeasureTheory

namespace InvRiskAlloc

open RiskPostpone.Threshold

/-- Proposition 5 and Table 4, pp. 16–17 (Hou–Lu, SSRN 4297536, accepted manuscript of MSOM
2024, doi:10.1287/msom.2022.0624): when `sΔS(q̂*_{β₂}) ≤ Δρ(Ψ) ≤ sΔS(q̂*_{β₁})`, the optimal
pre-order contract menus are those of Table 4, each the unique optimal solution of its problem:
P(1,2): `(q̂*_{β₁}, ρ_{β₁}(Ψ))` and `(q̂*_{β₂}, ρ_{β₂}(Ψ))`; P(1): `(q̂*_{β₁}, ρ_{β₁}(Ψ))`;
P(2): `(q̂*_{β₂}, ρ_{β₂}(Ψ))`. -/
theorem proposition_5 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Standing)
    (hlo : M.s * M.ΔS (M.qNW M.β₂) ≤ M.Δρ) (hhi : M.Δρ ≤ M.s * M.ΔS (M.qNW M.β₁)) :
    M.IsUniqueOpt12 ⟨M.qNW M.β₁, cvar M.μ M.β₁ M.Ψ, M.qNW M.β₂, cvar M.μ M.β₂ M.Ψ⟩ ∧
      M.IsUniqueOpt1 (M.qNW M.β₁, cvar M.μ M.β₁ M.Ψ) ∧
      M.IsUniqueOpt2 (M.qNW M.β₂, cvar M.μ M.β₂ M.Ψ) := by sorry

end InvRiskAlloc
