-- Prove2me | Theorems.Thm_InvRiskAlloc_proposition_4
-- name    : InvRiskAlloc.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:26.310933+00:00
-- url     : https://prove2.me/theorems/81f0da46-5df9-4305-9aaf-94839501031b
-- title:
--   Proposition 4, p. 16 (Table 3) — optimal pre-order menus for medium-to-high and high outside risk
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mu)$ is a probability space carrying the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity; $s$ is the selling price and $c$ the unit cost with $0<c<s$; $0<\beta_2<\beta_1\le 1$ are the two possible risk attitudes and $\nu\in(0,1)$ is the prior probability of $\beta_1$. Demand is nonnegative, its distribution function $F_D$ is continuous and strictly increasing on $[0,\infty)$, and $F_D^{-1}$ is its quantile; $\Psi\ge 0$ and $\rho_{\beta_1}(\Psi)$ is finite. $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ is the $\beta$-CVaR, $S_\beta(q)=\rho_\beta(\min\{q,D\})$, $\Delta S=S_{\beta_1}-S_{\beta_2}$, $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$, and $\hat q^*_\beta=q^{NW}_\beta=F_D^{-1}(\beta(1-c/s))$.
--
--   Suppose $\Delta\rho(\Psi)\ge s\Delta S(\hat q^*_{\beta_1})$. Let $\hat\beta_1=\big(1/\beta_1-\tfrac{1-\nu}{\nu}(1/\max\{\beta_2,(1-\nu c/s)\beta_1\}-1/\beta_1)\big)^{-1}$, $\hat q_1^{P(1,2):H}=F_D^{-1}(\hat\beta_1(s-c)/s)$ and $\hat q_1^{P(1,2):MH}=(\Delta S)^{-1}(\Delta\rho(\Psi)/s)$. Then the optimal pre-order contract menus are those of Table 3, each the unique optimal solution of its problem:
--
--   1. P(1,2), medium-to-high risk ($\Delta\rho(\Psi)\le s\Delta S(\hat q_1^{P(1,2):H})$): $q_1=\hat q_1^{P(1,2):MH}$, $U_1=\rho_{\beta_1}(\Psi)$, $q_2=\hat q^*_{\beta_2}$, $U_2=\rho_{\beta_2}(\Psi)$;
--   2. P(1,2), high risk ($\Delta\rho(\Psi)\ge s\Delta S(\hat q_1^{P(1,2):H})$): $q_1=\hat q_1^{P(1,2):H}$, $U_1=\rho_{\beta_1}(\Psi)$, $q_2=\hat q^*_{\beta_2}$, $U_2=\rho_{\beta_1}(\Psi)-s\Delta S(\hat q_1^{P(1,2):H})$;
--   3. P(1): if $\Delta\rho(\Psi)>s\Delta S(F_D^{-1}(\beta_1))$, P(1) is infeasible; otherwise $q_1=(\Delta S)^{-1}(\Delta\rho(\Psi)/s)$, $U_1=\rho_{\beta_1}(\Psi)$;
--   4. P(2): $q_2=\hat q^*_{\beta_2}$, $U_2=\rho_{\beta_2}(\Psi)$.
--
--   Here $(\Delta S)^{-1}(x)$ is a solution $q\in[0,F_D^{-1}(\beta_1)]$ of $\Delta S(q)=x$; each clause asserts that one exists and that every one gives the unique optimal menu.
--
--   When the outside opportunity is risky, the more risk-averse type wants to mimic the less risk-averse one, and the manufacturer distorts the latter's quantity upward, up to the cap $\hat q_1^{P(1,2):H}$ given by the virtual risk attitude $\hat\beta_1$.
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
--   - encoding: P(1) infeasible iff Δρ(Ψ) > sΔS(F_D^{-1}(β1)) → Δρ(Ψ) > sΔS(q) for every q ≥ 0 (then P(1) is infeasible); otherwise some q ≥ 0 has sΔS(q) ≥ Δρ(Ψ); reason: ΔS attains its maximum at F_D^{-1}(β1) and is constant beyond, so the two agree for β1 < 1; at β1 = 1 the paper’s F_D^{-1}(1) = +∞ means the supremum, which this form expresses without a junk quantile
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), Proposition 4 and Table 3, p. 16

import Mathlib
import Definitions.Def_InvRiskAlloc_Model

open MeasureTheory

namespace InvRiskAlloc

open RiskPostpone.Threshold

/-- Proposition 4 and Table 3, p. 16 (Hou–Lu, SSRN 4297536, accepted manuscript of MSOM 2024,
doi:10.1287/msom.2022.0624): when `Δρ(Ψ) ≥ sΔS(q̂*_{β₁})`, the optimal pre-order contract
menus are those of Table 3, each the unique optimal solution of its problem:

1. P(1,2), Medium-to-High (`Δρ(Ψ) ≤ sΔS(q̂₁^{P(1,2):H})`):
   `q₁ = q̂₁^{P(1,2):MH} = (ΔS)⁻¹(Δρ(Ψ)/s)`, `U₁ = ρ_{β₁}(Ψ)`, `q₂ = q̂*_{β₂}`,
   `U₂ = ρ_{β₂}(Ψ)`;
2. P(1,2), High (`Δρ(Ψ) ≥ sΔS(q̂₁^{P(1,2):H})`): `q₁ = q̂₁^{P(1,2):H}`, `U₁ = ρ_{β₁}(Ψ)`,
   `q₂ = q̂*_{β₂}`, `U₂ = ρ_{β₁}(Ψ) − sΔS(q̂₁^{P(1,2):H})`;
3. P(1): if `Δρ(Ψ) > sΔS(F_D⁻¹(β₁))`, P(1) is infeasible; otherwise
   `q₁ = (ΔS)⁻¹(Δρ(Ψ)/s)`, `U₁ = ρ_{β₁}(Ψ)`;
4. P(2): `q₂ = q̂*_{β₂}`, `U₂ = ρ_{β₂}(Ψ)`.

Here `β̂₁ = (1/β₁ − (1 − ν)/ν·(1/max{β₂, (1 − νc/s)β₁} − 1/β₁))⁻¹` and
`q̂₁^{P(1,2):H} = F_D⁻¹(β̂₁(s − c)/s)`.

**Formalization Note** `(ΔS)⁻¹(x)` is a solution `q` of `ΔS(q) = x` with `0 ≤ q` and
`F_D(q) ≤ β₁` (`Model.IsDeltaSInv`). Since `ΔS` is largest at `F_D⁻¹(β₁)` and constant beyond,
the condition `Δρ(Ψ) > sΔS(F_D⁻¹(β₁))` is written `Δρ(Ψ) > sΔS(q)` for every `q ≥ 0`; this is
the paper's condition for `β₁ < 1` and gives `F_D⁻¹(1) = +∞` its meaning at `β₁ = 1`. -/
theorem proposition_4 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Standing)
    (hΔ : M.s * M.ΔS (M.qNW M.β₁) ≤ M.Δρ) :
    (M.Δρ ≤ M.s * M.ΔS M.qH1 →
      (∃ q, M.IsDeltaSInv q (M.Δρ / M.s)) ∧
        ∀ q, M.IsDeltaSInv q (M.Δρ / M.s) →
          M.IsUniqueOpt12 ⟨q, cvar M.μ M.β₁ M.Ψ, M.qNW M.β₂, cvar M.μ M.β₂ M.Ψ⟩) ∧
    (M.s * M.ΔS M.qH1 ≤ M.Δρ →
      M.IsUniqueOpt12 ⟨M.qH1, cvar M.μ M.β₁ M.Ψ, M.qNW M.β₂,
        cvar M.μ M.β₁ M.Ψ - M.s * M.ΔS M.qH1⟩) ∧
    ((∀ q, 0 ≤ q → M.s * M.ΔS q < M.Δρ) → M.Feasible1 = ∅) ∧
    ((∃ q, 0 ≤ q ∧ M.Δρ ≤ M.s * M.ΔS q) →
      (∃ q, M.IsDeltaSInv q (M.Δρ / M.s)) ∧
        ∀ q, M.IsDeltaSInv q (M.Δρ / M.s) → M.IsUniqueOpt1 (q, cvar M.μ M.β₁ M.Ψ)) ∧
    M.IsUniqueOpt2 (M.qNW M.β₂, cvar M.μ M.β₂ M.Ψ) := by sorry

end InvRiskAlloc
