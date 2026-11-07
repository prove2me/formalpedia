-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_B_2
-- name    : IIDMatchHard.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:11.178239+00:00
-- url     : https://prove2.me/theorems/dc891624-42f1-42ff-b18e-0965a4acdc1b
-- title:
--   Lemma B.2 — blocked arrivals are rare
-- statement:
--   In the adjusted Poisson model of $I(G,\lambda)$, with $G$ simple and $\lambda>0$:
--
--   1. Let $e=(u,v)$ be an edge and $t\in[0,1]$. The event $D_e(t)$ is independent of the family $(X_w(t))_{w\in V}$, and
--   $$P_e(t)=\exp\big(-2\lambda t(\deg(u)+\deg(v)-1)\big)\ \ge\ 1-4\Delta_G\lambda t.$$
--   2. The expected number of blocked arrivals among $y_1,\dots,y_{K(1)}$ is at most $4\Delta_G\lambda^2m$.
--
--   Blocking changes the value of a policy by $O(\lambda^2 m)$, which is small when $\lambda$ is small.
--
--   Differences from the source:
--   - encoding: independence of the event D_e(t) and the numbers X_w(t) → IndepFun of the real indicator of D_e(t) and the vector (X_w(t))_w; reason: an event is independent of a family iff its indicator is
--   - encoding: the expected number of blocked arrivals → a lower Lebesgue integral of the count, bounded by ENNReal.ofReal of the bound; reason: the count is nonnegative; same value
--   - encoding: P_e(t), the probability that an arrival of type e^s is not blocked → computed for the sign +; reason: blocking does not depend on the sign
--   - encoding: the adjusted Poisson model (a Poisson process of rate R with i.i.d. types) → the law cutLaw on (ℝ × Y)^ℕ, i.i.d. exponential gaps with independent types, K(t) the Set.ncard of {k : τ_{k+1} ≤ t}, arrivals 0-based; reason: the same process; K(t) differs only on a null event (infinitely many points, or a negative gap)
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma B.2, p.15 (PDF p.16)

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace IIDMatchHard

/-- **Lemma B.2 (Blocked arrivals).** (a) Let `e = (u, v)` be an edge of `G` and `t ∈ [0, 1]`.
The event `D_e(t)` is independent of the numbers `X_w(t)`, `w ∈ V`, and
`P_e(t) = exp(−2λt(deg(u) + deg(v) − 1)) ≥ 1 − 4∆_G λ t`. (b) The expected number of blocked
arrivals among `y_1, …, y_{K(1)}` is at most `4∆_G λ² m`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma B.2, p.15 (PDF p.16).

**Formalization Note.** The model is the adjusted Poisson model of `I(G, λ)` for a simple graph
`G` and `λ > 0`. Independence is of the indicator of `D_e(t)` and the vector `(X_w(t))_{w ∈ V}`.
The expected count in (b) is a lower Lebesgue integral of the nonnegative count. -/
theorem lemma_B_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lam : ℝ)
    (hlam : 0 < lam) :
    (∀ (u v : V) (huv : G.Adj u v) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      IndepFun (fun ω => (blockEvent G s(u, v) t).indicator (fun _ => (1 : ℝ)) ω)
          (fun ω (w : V) => vtxCount G ω t w) (cutLaw G lam) ∧
        probUnblocked G lam ⟨s(u, v), G.mem_edgeSet.2 huv⟩ t =
          Real.exp (-(2 * lam * t *
            (((G.neighborSet u).ncard : ℝ) + ((G.neighborSet v).ncard : ℝ) - 1))) ∧
        1 - 4 * (maxDeg G : ℝ) * lam * t ≤
          Real.exp (-(2 * lam * t *
            (((G.neighborSet u).ncard : ℝ) + ((G.neighborSet v).ncard : ℝ) - 1)))) ∧
    ∫⁻ ω, (blockedCount G ω : ENNReal) ∂ cutLaw G lam ≤
      ENNReal.ofReal (4 * (maxDeg G : ℝ) * lam ^ 2 * (numEdges G : ℝ)) := by sorry

end IIDMatchHard
