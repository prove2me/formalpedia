-- Prove2me | Theorems.Thm_HSOSetCover_FullCover_Supplement_theorem_4
-- name    : HSOSetCover.FullCover.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:16:15.538994+00:00
-- url     : https://prove2.me/theorems/05746fd3-d1c5-4bea-aef2-12198f7dabed
-- title:
--   Theorem 4 — one-turn partial-cover success bound and the greedy multicover guarantee
-- statement:
--   Consider the one-turn model of §5: a WSC instance with $n=|U|$, a target $\rho\ge1$, a feasible dual $y$, oracles $[k]$ with known sets $V_i$ satisfying $\bigcup_iV_i=U$, $p,\eta\in(0,1)$, $q=1-p$, and a deadline $D>0$. For every call-count vector $\zeta$, the one-turn batch (on a probability space, with a fixed processing order and no independence assumption) has calls of latency at most $D$ and token cost $0<\mathrm{TOK}_{i,a}\le c_i$ almost surely, and it satisfies the history-conditional guarantee with parameter $p$.
--
--   1. For every $\zeta$, the PTM returns a certified $\rho$-cover by $D$ with probability at least
--   $$\max\Big\{0,\ 1-\sum_{e\in U}q^{d_e(\zeta)}\Big\},$$
--   and its token cost is at most $c(\zeta)$ almost surely.
--   2. The greedy multicover algorithm with threshold $r_1$, started at $\zeta=0$ and with any tie-break, has the following properties:
--      1. it makes at most $nr_1$ increments, each of which evaluates the $k$ marginals $\Delta_i$ by scanning $V_i$;
--      2. it never stalls before $\Phi(\zeta)=nr_1$;
--      3. every vector $\zeta'$ it outputs has a one-turn batch that returns a certified $\rho$-cover by $D$ with probability at least $\eta$, and
--   $$c(\zeta')\le\big(1+\ln(nr_1)\big)\,\lceil r_1/r_0\rceil\,\mathrm{OPT}^{\mathrm{risk}}_\eta .$$
--
--   For fixed $p$ and $\eta$ the factor is $O(\log^2n)$ relative to $\mathrm{OPT}^{\mathrm{risk}}_\eta$.
--
--   Differences from the source:
--   - reading: a greedy algorithm computes ζ′ in time polynomial in n, k, and the numerical value of r_1 → the greedy step relation (any tie-break) from ζ = 0 makes at most n·r_1 increments, never stalls before Φ = n r_1, and each step evaluates the k marginals Δ_i as counts over V_i; reason: unit-cost arithmetic model of the proof ("each marginal can be computed by scanning V_i"); in a bit model the stated bound would ignore the bit length of the c_i
--   - encoding: every positive-probability history of earlier processed responses, conditional probability at least p → for the exact list h of earlier processed responses with μ(history = h) > 0, μ(E ∩ {history = h}) ≥ p μ(history = h); reason: responses are finite-valued, so conditioning on a history is elementary; multiplicative form
--   - encoding: returns a certified ρ-cover by D → the retained family is a certified ρ-cover and every call has latency at most D; reason: one turn whose calls all finish by D
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, Theorem 4, PDF p. 10 / printed p. 9; proof PDF pp. 10–11 / printed pp. 9–10; model PDF p. 9

import Mathlib
import Definitions.Def_HSOSetCover_FullCover_Supplement_OneTurn

open MeasureTheory

namespace HSOSetCover.FullCover.Supplement

/-- **Theorem 4**, PDF p. 10 / printed p. 9 (proof PDF pp. 10–11). Setting of §5 (PDF p. 9): a WSC
instance, `ρ ≥ 1`, a feasible dual vector `y`, oracles `[k]` with known sets `V_i ⊆ U`,
`⋃_i V_i = U`, `p, η ∈ (0,1)`, `q = 1 - p`, deadline `D > 0`; for every call-count vector `ζ` a
one-turn batch (on a probability space) whose calls have latency at most `D`, token cost
`0 < TOK_{i,a} ≤ c_i` almost surely, and satisfy the history-conditional guarantee with parameter
`p` for the fixed processing order.

(1) For every `ζ`, the PTM returns a certified `ρ`-cover by `D` with probability at least
`max{0, 1 - ∑_e q^{d_e(ζ)}}` and its token cost is at most `c(ζ)` almost surely.

(2) The greedy multicover algorithm (any tie-break), started at `ζ = 0`, makes at most `n r₁`
increments (each evaluating the `k` marginals `Δ_i` by a scan of `V_i`), never gets stuck before
`Φ(ζ) = n r₁`, and every vector `ζ'` it outputs has a one-turn batch returning a certified
`ρ`-cover by `D` with probability at least `η` and `c(ζ') ≤ (1 + ln(n r₁)) ⌈r₁/r₀⌉ OPT^risk_η`. -/
theorem theorem_4 {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι]
    (W : WSCInstance U ι) (ρ : ℝ) (hρ : 1 ≤ ρ) (y : U → ℝ) (hy : W.DualFeasible y)
    {k : ℕ} (V : Fin k → Finset U) (hV : ∀ e, ∃ i, e ∈ V i) (c : Fin k → ℝ)
    (p η D : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) (hη₀ : 0 < η) (hη₁ : η < 1) (hD : 0 < D)
    {Ω : Type*} [MeasurableSpace Ω] (μ : (Fin k → ℕ) → Measure Ω)
    [hμ : ∀ ζ, IsProbabilityMeasure (μ ζ)]
    (B : (ζ : Fin k → ℕ) → OneTurnBatch ι ζ Ω)
    (htok : ∀ ζ a, ∀ᵐ ω ∂(μ ζ), 0 < (B ζ).tok a ω ∧ (B ζ).tok a ω ≤ c a.1)
    (hlat : ∀ ζ a, ∀ᵐ ω ∂(μ ζ), (B ζ).lat a ω ≤ D)
    (hguar : ∀ ζ, (B ζ).HistoryGuarantee W ρ y V p (μ ζ)) :
    (∀ ζ : Fin k → ℕ,
      ENNReal.ofReal (max 0 (1 - riskSum V p ζ)) ≤ μ ζ ((B ζ).successEvent W ρ y D) ∧
      ∀ᵐ ω ∂(μ ζ), (B ζ).totalTok ω ≤ batchBound c ζ) ∧
    (∀ (T : ℕ) (seq : ℕ → Fin k → ℕ), seq 0 = 0 →
      (∀ t < T, GreedyStep V c (r1 U p η) (seq t) (seq (t + 1))) →
        T ≤ Fintype.card U * r1 U p η) ∧
    (∀ ζ, Relation.ReflTransGen (GreedyStep V c (r1 U p η)) 0 ζ →
      coverPotential V (r1 U p η) ζ < Fintype.card U * r1 U p η →
        ∃ ζ', GreedyStep V c (r1 U p η) ζ ζ') ∧
    (∀ ζ', Relation.ReflTransGen (GreedyStep V c (r1 U p η)) 0 ζ' →
      ¬ coverPotential V (r1 U p η) ζ' < Fintype.card U * r1 U p η →
        ENNReal.ofReal η ≤ μ ζ' ((B ζ').successEvent W ρ y D) ∧
        batchBound c ζ' ≤ (1 + Real.log (Fintype.card U * r1 U p η)) *
          ⌈(r1 U p η : ℝ) / r0 p η⌉₊ * optRisk V c p η) := by sorry

end HSOSetCover.FullCover.Supplement
