-- Prove2me | Theorems.Thm_HSOSetCover_FullCover_Supplement_theorem_5
-- name    : HSOSetCover.FullCover.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:16:53.888022+00:00
-- url     : https://prove2.me/theorems/f486417e-738f-4773-bab4-b512c24a23c3
-- title:
--   Theorem 5 — adaptive upper bounds $\eta_U(u)$, $\mathrm{TOK}_U(u)$ and lower bounds via revealed coverage
-- statement:
--   Consider the adaptive model of §6: a WSC instance with $n=|U|$, $\rho\ge1$, a feasible dual $y$, integers $1\le a\le b\le n$, probabilities $\underline p,\overline p\in(0,1]$, token-cost bounds $0<\underline c\le\overline c$, latency bounds $0<\underline\ell\le\overline\ell$, a deadline $D>0$, $r_a=\lceil n/a\rceil$ and $r_b=\lceil n/b\rceil$. Response laws may depend on the residual and the transcript, and no independence is assumed.
--
--   1. Suppose the run of the adaptive selection-only policy $\pi$ satisfies the upper-policy conditions. Then for every integer $u$ with $u\overline\ell\le D$, running $\pi$ until it completes or has used $u$ turns returns a certified $\rho$-cover by $D$ with probability at least $\eta_U(u)=\mathbb P[\mathrm{Bin}(u,\underline p)\ge r_a]$, and its expected token cost is at most
--   $$\mathrm{TOK}_U(u)=\overline c\sum_{t=0}^{u-1}\mathbb P[\mathrm{Bin}(t,\underline p)<r_a].$$
--   2. Suppose a selection-only PTM with turn bound $u$ is deadline- and turn-feasible, satisfies the universal batch limitations on revealed coverage, and returns a certified $\rho$-cover by $D$ with probability at least $\eta$. Then its expected token cost is at least $\eta r_b\underline c/\overline p$, and, with $v=\min\{u,\lfloor D/\underline\ell\rfloor\}$,
--   $$\eta\le\mathbb P[\mathrm{Bin}(v,\overline p)\ge r_b].$$
--
--   When both sets of conditions hold and $\eta\le\eta_U(u)$, the instance-level token complexity therefore lies between $\eta r_b\underline c/\overline p$ and $\mathrm{TOK}_U(u)$.
--
--   Differences from the source:
--   - reading: conditional on every reached positive-probability history and each batch selected with positive conditional probability → conditional on the information F_t on the reached event: for every A ∈ F_t inside it, μ(A ∩ E) ≥ p̲ μ(A) (resp. ≤ p̄ μ(A)) and ∫_A TOK_t ≤ c̄ μ(A) (resp. ≥ c̲ μ(A)); the coverage and latency clauses almost surely on the reached event; reason: the form the proof (PDF p. 16) uses; equivalent for countable transcripts
--   - generalization: the run of the policy π, resp. of a selection-only PTM → any filtered process (reached events, retained resp. proposed and returned families, token costs, latencies) satisfying the structural axioms of such a run; reason: every actual run satisfies the axioms, so the statement specializes to the source
--   - reading: deadline- and turn-feasible: at most u turns before D, unfinished calls canceled at D → no turn t ≥ u is reached, and a turn proposes sets only if it finishes by D (turn t finishes at Lat_0 + … + Lat_t); reason: a canceled call returns nothing; the lower bound covers every such PTM
--   - encoding: turns t = 1, …, u; real token costs → turns t = 0, …, u − 1; token costs in [0, ∞]; reason: relabelling; expectations of nonnegative costs
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, Theorem 5, PDF p. 12 / printed p. 11; proof Appendix A.5, PDF p. 16 / printed p. 15; model PDF pp. 11–12

import Mathlib
import Definitions.Def_HSOSetCover_FullCover_Supplement_Adaptive

open MeasureTheory

namespace HSOSetCover.FullCover.Supplement

/-- **Theorem 5**, PDF p. 12 / printed p. 11 (proof Appendix A.5, PDF p. 16), both parts. Setting
of §6 (PDF pp. 11–12): a WSC instance with `n = |U|`, `ρ ≥ 1`, a feasible dual vector `y`, integers
`1 ≤ a ≤ b ≤ n`, `p̲, p̄ ∈ (0,1]`, `0 < c̲ ≤ c̄`, `0 < ℓ̲ ≤ ℓ̄`, a deadline `D > 0`,
`r_a = ⌈n/a⌉`, `r_b = ⌈n/b⌉`.

(1) If the run of the adaptive policy `π` satisfies the upper-policy conditions, then for every
integer `u` with `u ℓ̄ ≤ D`, running `π` until it completes or has used `u` turns returns a
certified `ρ`-cover by `D` with probability at least `η_U(u) = ℙ[Bin(u, p̲) ≥ r_a]` and has
expected token cost at most `TOK_U(u) = c̄ ∑_{t=0}^{u-1} ℙ[Bin(t, p̲) < r_a]`.

(2) If the run of a selection-only PTM satisfies the universal batch limitations and is deadline-
and turn-feasible with turn bound `u`, and it returns a certified `ρ`-cover by `D` with probability
at least `η`, then its expected token cost is at least `η r_b c̲ / p̄`, and
`η ≤ ℙ[Bin(v, p̄) ≥ r_b]` with `v = min{u, ⌊D/ℓ̲⌋}`. -/
theorem theorem_5 {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι]
    (W : WSCInstance U ι) (ρ : ℝ) (hρ : 1 ≤ ρ) (y : U → ℝ) (hy : W.DualFeasible y)
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ Fintype.card U)
    (pLow pHigh cLow cHigh lLow lHigh D : ℝ)
    (hpLow₀ : 0 < pLow) (hpLow₁ : pLow ≤ 1) (hpHigh₀ : 0 < pHigh) (hpHigh₁ : pHigh ≤ 1)
    (hcLow : 0 < cLow) (hc : cLow ≤ cHigh) (hlLow : 0 < lLow) (hl : lLow ≤ lHigh) (hD : 0 < D) :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ π : PolicyRun W ρ y Ω, π.UpperPolicyConditions μ a pLow cHigh lHigh →
        ∀ u : ℕ, (u : ℝ) * lHigh ≤ D →
          ENNReal.ofReal (etaU u pLow ⌈(Fintype.card U : ℚ) / a⌉₊) ≤ μ (π.successWithin u D) ∧
          ∫⁻ ω, π.costWithin u ω ∂μ ≤
            ENNReal.ofReal (tokU u pLow cHigh ⌈(Fintype.card U : ℚ) / a⌉₊)) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ (M : SelectionRun W Ω) (u : ℕ) (η : ℝ),
        M.UniversalBatchLimitations μ b pHigh cLow lLow → M.DeadlineTurnFeasible u D →
        ENNReal.ofReal η ≤ μ (M.successEvent ρ) →
          ENNReal.ofReal (η * ⌈(Fintype.card U : ℚ) / b⌉₊ * cLow / pHigh) ≤
              ∫⁻ ω, M.totalCost u ω ∂μ ∧
            η ≤ binomTailGe (min u ⌊D / lLow⌋₊) pHigh ⌈(Fintype.card U : ℚ) / b⌉₊) := by sorry

end HSOSetCover.FullCover.Supplement
