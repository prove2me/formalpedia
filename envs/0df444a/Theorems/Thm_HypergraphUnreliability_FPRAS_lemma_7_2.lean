-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_7_2
-- name    : HypergraphUnreliability.FPRAS.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:26.054968+00:00
-- url     : https://prove2.me/theorems/f8f0b0e4-364d-4206-81cf-9cb1cd4c33db
-- title:
--   Lemma 7.2 — Euler and horizon total variation errors
-- statement:
--   Assume the standing context, positive rational rates $r$, and $\Lambda$ the minimum cut.
--
--   **General rate bound.** If $\sum_e r_e\le M$, $L\ge1$, $h=t/L$, $t\ge0$ and $Mh\le1$, then $L$ exact Euler steps are within
--   $$\frac{M^2t^2}{L}$$
--   of $R_w$ at time $t$ in total variation, and $R_w$ at times $t_1,t_2\ge0$ differ by at most $M|t_1-t_2|$.
--
--   **The printed statement.** With exact categorical draws and the parameters (7.2) of the common-probability algorithm, the total variation distance between $L$ Euler steps and $R_w$ at time $T^\prime$ is at most
--   $$\frac{m^2(T^\prime)^2}{L}\le\frac{\varepsilon}{128N},$$
--   and the distance between $R_w$ at times $T^\prime$ and $T=\log(1/p)$ is at most $m|T-T^\prime|\le\varepsilon/(128N)$.
--
--   The general layer at $M=R$, $t=1$ is the bound $R^2/L^\prime$ of §9.4.
--
--   Differences from the source:
--   - generalization: Euler error with rate bound $m$ and the common parameters → in addition a general rate bound $M\ge\sum_e r_e$ and horizon $t$; reason: §9.4 uses it at $M=R$, horizon $1$; the printed statement is the third clause, unchanged
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 7.2, p. 9; (7.2), p. 9; §9.4, p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_EulerSampler
import Definitions.Def_HypergraphUnreliability_FPRAS_CommonAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 7.2, p. 9, in two layers.

General rate bound (used at `M = m` here and at `M = R`, horizon `1`, in §9.4, p. 14): if the rates are
positive, `Λ` is the minimum cut, `∑_e r e ≤ M`, `L ≥ 1`, `h = t/L` and `M h ≤ 1`, then `L` exact Euler
steps are within `M² t² / L` of `R_w` at time `t` in total variation; and `R_w` at two horizons differ
by at most `M |t₁ - t₂|`.

The printed statement, for the common-probability parameters (7.2): `L` Euler steps and `R_w` at time
`T′` differ by at most `m² T′² / L ≤ ε/(128 N)`, and `R_w` at times `T′, T` differ by at most
`m |T - T′| ≤ ε/(128 N)`, where `T = log(1/p)`. -/
theorem lemma_7_2 :
    (∀ {n m : ℕ} (P : SamplerParams n m), P.H.Standing → (∀ e, 0 < P.r e) →
      P.Λ = P.H.minCut P.r →
      ∀ (w : VertexPair n) (M t : ℚ), ∑ e, P.r e ≤ M → 0 ≤ t → 1 ≤ P.L → P.h = t / P.L →
        M * P.h ≤ 1 →
        tvDist (P.eulerLawReal w) (chainLaw (P.chainRate w) (some MarkedState.init) t) ≤
          ((M ^ 2 * t ^ 2 / P.L : ℚ) : ℝ)) ∧
    (∀ {n m : ℕ} (P : SamplerParams n m), P.H.Standing → (∀ e, 0 < P.r e) →
      P.Λ = P.H.minCut P.r →
      ∀ (w : VertexPair n) (M : ℝ) (t₁ t₂ : ℝ), ∑ e, ((P.r e : ℚ) : ℝ) ≤ M → 0 ≤ t₁ → 0 ≤ t₂ →
        tvDist (chainLaw (P.chainRate w) (some MarkedState.init) t₁)
            (chainLaw (P.chainRate w) (some MarkedState.init) t₂) ≤ M * |t₁ - t₂|) ∧
    (∀ x : CommonInstance, x.Valid → x.IsSamplingCase → ∀ w : VertexPair x.graph.n,
      tvDist (x.params.eulerLawReal w)
          (chainLaw (x.params.chainRate w) (some MarkedState.init) ((x.T' : ℚ) : ℝ)) ≤
        (((x.m : ℚ) ^ 2 * x.T' ^ 2 / x.L : ℚ) : ℝ) ∧
      (x.m : ℚ) ^ 2 * x.T' ^ 2 / x.L ≤ x.ε.val / (128 * x.N) ∧
      tvDist (chainLaw (x.params.chainRate w) (some MarkedState.init) ((x.T' : ℚ) : ℝ))
          (chainLaw (x.params.chainRate w) (some MarkedState.init)
            (Real.log ((x.p.den : ℝ) / x.p.num))) ≤
        (x.m : ℝ) * |Real.log ((x.p.den : ℝ) / x.p.num) - ((x.T' : ℚ) : ℝ)| ∧
      (x.m : ℝ) * |Real.log ((x.p.den : ℝ) / x.p.num) - ((x.T' : ℚ) : ℝ)| ≤
        ((x.ε.val / (128 * x.N) : ℚ) : ℝ)) := by sorry

end HypergraphUnreliability.FPRAS
