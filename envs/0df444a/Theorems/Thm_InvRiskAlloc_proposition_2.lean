-- Prove2me | Theorems.Thm_InvRiskAlloc_proposition_2
-- name    : InvRiskAlloc.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:17.171095+00:00
-- url     : https://prove2.me/theorems/52e0ec62-fb41-4a49-bb27-0398b034d219
-- title:
--   Proposition 2, p. 13 (Table 2) — optimal pre-order menus for low and low-to-medium outside risk
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mu)$ is a probability space carrying the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity; $s$ is the selling price and $c$ the unit cost with $0<c<s$; $0<\beta_2<\beta_1\le 1$ are the two possible risk attitudes and $\nu\in(0,1)$ is the prior probability of $\beta_1$. Demand is nonnegative, its distribution function $F_D$ is continuous and strictly increasing on $[0,\infty)$, and $F_D^{-1}$ is its quantile; $\Psi\ge 0$ and $\rho_{\beta_1}(\Psi)$ is finite. $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ is the $\beta$-CVaR, $S_\beta(q)=\rho_\beta(\min\{q,D\})$, $\Delta S=S_{\beta_1}-S_{\beta_2}$, $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$, and $\hat q^*_\beta=q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$.
--
--   Suppose $\Delta\rho(\Psi)\le s\Delta S(\hat q^*_{\beta_2})$. Let $\hat\beta_2=\big(1/\beta_2+\tfrac{\nu}{1-\nu}(1/\beta_2-1/\beta_1)\big)^{-1}$, $\hat q_2^{P(1,2):L}=F_D^{-1}(\hat\beta_2(s-c)/s)$ and $\hat q_2^{P(1,2):LM}=(\Delta S)^{-1}(\Delta\rho(\Psi)/s)$. Then the optimal pre-order contract menus are those of Table 2, each the unique optimal solution of its problem:
--
--   1. P(1,2), low risk ($\Delta\rho(\Psi)\le s\Delta S(\hat q_2^{P(1,2):L})$): $q_1=\hat q^*_{\beta_1}$, $U_1=\rho_{\beta_2}(\Psi)+s\Delta S(\hat q_2^{P(1,2):L})$, $q_2=\hat q_2^{P(1,2):L}$, $U_2=\rho_{\beta_2}(\Psi)$;
--   2. P(1,2), low-to-medium risk ($s\Delta S(\hat q_2^{P(1,2):L})\le\Delta\rho(\Psi)$): $q_1=\hat q^*_{\beta_1}$, $U_1=\rho_{\beta_1}(\Psi)$, $q_2=\hat q_2^{P(1,2):LM}$, $U_2=\rho_{\beta_2}(\Psi)$;
--   3. P(1): $q_1=\hat q^*_{\beta_1}$, $U_1=\rho_{\beta_1}(\Psi)$;
--   4. P(2): $q_2=(\Delta S)^{-1}(\Delta\rho(\Psi)/s)$, $U_2=\rho_{\beta_2}(\Psi)$.
--
--   Here $(\Delta S)^{-1}(x)$ is a solution $q\in[0,F_D^{-1}(\beta_1)]$ of $\Delta S(q)=x$; the statement asserts that such a solution exists and that every one of them gives the unique optimal menu.
--
--   When the outside opportunity is not risky, the less risk-averse type wants to mimic the other one, and the manufacturer distorts the more risk-averse type's quantity downward.
--
--   Differences from the source:
--
--   - reading: D is supported on [0,∞) (p. 8) → the support is all of [0,∞): F_D strictly increasing on [0,∞); reason: with a gap in the support η(β2) need not exist (D uniform on [0,1]∪[2,3], s = 1, c = 1/2, ν = 1/2, β2 = 1/2: the left side of η’s equation jumps from 0.75 to 1.25 at η′ = 1, past the right side 1); the weaker reading D ≥ 0 makes §4.3.1 false
--   - generalization: D has distribution F_D and density f_D (p. 8) → D measurable, D ≥ 0 a.s., F_D continuous and strictly increasing on [0,∞); no density; reason: a full-support law with a density satisfies these hypotheses, so the source’s setting is a special case
--   - encoding: c < s (p. 8) → 0 < c < s; reason: at c = 0 the first-best quantity F_D^{-1}(1) and the interval [1, s/(s−c)] are undefined; the case is excluded, not a valid instance
--   - encoding: Ψ ≥ 0 and ρ_β(Ψ) a real number (pp. 8, 12) → Ψ measurable, Ψ ≥ 0 a.s., and β1 < 1 or Ψ integrable; reason: for Ψ ≥ 0 and β < 1 the CVaR is finite; at β1 = 1 it is E[Ψ], so the disjunction excludes only ρ_β1(Ψ) = +∞, which the real-valued IR constraints already exclude
--   - reading: the optimal pre-order contract menu is given in Table k → each table entry is an optimal solution and every optimal solution equals it; reason: the stronger reading of "the optimal menu"; the numerical checks of the planning session found no ties
--   - encoding: P(1) and P(2), (2)–(3), maximize over q, U without q ≥ 0 → q ≥ 0 in P(1) and P(2); reason: q is an order quantity; (1) and §3.2.1 state q ≥ 0
--   - encoding: (ΔS)^{-1}(Δρ(Ψ)/s) → a solution q of ΔS(q) = Δρ(Ψ)/s with q ≥ 0 and F_D(q) ≤ β1; the statement asserts a solution exists and every solution gives the optimal menu; reason: ΔS is strictly increasing on [0, F_D^{-1}(β1)] and constant beyond, so this is the inverse the paper means; F_D(q) ≤ β1 avoids evaluating F_D^{-1}(1) when β1 = 1
--   - encoding: Low row: Δρ(Ψ) ∈ [0, sΔS(q̂_2^{P(1,2):L})] → Δρ(Ψ) ≤ sΔS(q̂_2^{P(1,2):L}); reason: Δρ(Ψ) ≥ 0 holds under the standing assumptions (CVaR increases in β), so the lower end excludes no instance
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), Proposition 2, p. 13, and Table 2, p. 14

import Mathlib
import Definitions.Def_InvRiskAlloc_Model

open MeasureTheory

namespace InvRiskAlloc

open RiskPostpone.Threshold

/-- Proposition 2 and Table 2, pp. 13–14 (Hou–Lu, SSRN 4297536, accepted manuscript of MSOM
2024, doi:10.1287/msom.2022.0624): when `Δρ(Ψ) ≤ sΔS(q̂*_{β₂})`, the optimal pre-order contract
menus are those of Table 2, each the unique optimal solution of its problem:

1. P(1,2), Low (`Δρ(Ψ) ≤ sΔS(q̂₂^{P(1,2):L})`): `q₁ = q̂*_{β₁}`,
   `U₁ = ρ_{β₂}(Ψ) + sΔS(q̂₂^{P(1,2):L})`, `q₂ = q̂₂^{P(1,2):L}`, `U₂ = ρ_{β₂}(Ψ)`;
2. P(1,2), Low-to-Medium (`sΔS(q̂₂^{P(1,2):L}) ≤ Δρ(Ψ)`): `q₁ = q̂*_{β₁}`, `U₁ = ρ_{β₁}(Ψ)`,
   `q₂ = q̂₂^{P(1,2):LM} = (ΔS)⁻¹(Δρ(Ψ)/s)`, `U₂ = ρ_{β₂}(Ψ)`;
3. P(1): `q₁ = q̂*_{β₁}`, `U₁ = ρ_{β₁}(Ψ)`;
4. P(2): `q₂ = (ΔS)⁻¹(Δρ(Ψ)/s)`, `U₂ = ρ_{β₂}(Ψ)`.

Here `β̂₂ = (1/β₂ + ν/(1 − ν)(1/β₂ − 1/β₁))⁻¹` and `q̂₂^{P(1,2):L} = F_D⁻¹(β̂₂(s − c)/s)`.

**Formalization Note** `(ΔS)⁻¹(x)` is a solution `q` of `ΔS(q) = x` with `0 ≤ q` and
`F_D(q) ≤ β₁` (`Model.IsDeltaSInv`); each such clause asserts that a solution exists and that
every solution yields the unique optimal menu. -/
theorem proposition_2 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Standing)
    (hΔ : M.Δρ ≤ M.s * M.ΔS (M.qNW M.β₂)) :
    (M.Δρ ≤ M.s * M.ΔS M.qL2 →
      M.IsUniqueOpt12 ⟨M.qNW M.β₁, cvar M.μ M.β₂ M.Ψ + M.s * M.ΔS M.qL2, M.qL2,
        cvar M.μ M.β₂ M.Ψ⟩) ∧
    (M.s * M.ΔS M.qL2 ≤ M.Δρ →
      (∃ q, M.IsDeltaSInv q (M.Δρ / M.s)) ∧
        ∀ q, M.IsDeltaSInv q (M.Δρ / M.s) →
          M.IsUniqueOpt12 ⟨M.qNW M.β₁, cvar M.μ M.β₁ M.Ψ, q, cvar M.μ M.β₂ M.Ψ⟩) ∧
    M.IsUniqueOpt1 (M.qNW M.β₁, cvar M.μ M.β₁ M.Ψ) ∧
    ((∃ q, M.IsDeltaSInv q (M.Δρ / M.s)) ∧
      ∀ q, M.IsDeltaSInv q (M.Δρ / M.s) → M.IsUniqueOpt2 (q, cvar M.μ M.β₂ M.Ψ)) := by sorry

end InvRiskAlloc
