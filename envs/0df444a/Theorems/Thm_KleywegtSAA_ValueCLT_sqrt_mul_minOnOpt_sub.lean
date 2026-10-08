-- Prove2me | Theorems.Thm_KleywegtSAA_ValueCLT_sqrt_mul_minOnOpt_sub
-- name    : KleywegtSAA.ValueCLT.sqrt_mul_minOnOpt_sub
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:49.094067+00:00
-- url     : https://prove2.me/theorems/e724d56f-f0c5-4673-935d-1c613e4889e8
-- title:
--   §2.2, p. 5 — √N[min_{x∈𝒮*} ĝ_N(x) − v*] = min_{x∈𝒮*}{√N[ĝ_N(x) − g(x)]}
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $g$ the true objective, $v^* = \min_{x \in \mathcal S} g(x)$, $\mathcal S^*$ the set of minimizers of $g$, and $\hat g_N$ the sample average function. Since $v^* = g(x)$ for every $x \in \mathcal S^*$, for every sample size $N$ and every realization of the sample
--   $$\sqrt N \Big[\min_{x \in \mathcal S^*} \hat g_N(x) - v^*\Big] = \min_{x \in \mathcal S^*} \Big\{\sqrt N\,\big[\hat g_N(x) - g(x)\big]\Big\}.$$
--
--   The identity expresses the centred and scaled minimum over $\mathcal S^*$ as a continuous function (the minimum) of the vector of scaled deviations $\sqrt N[\hat g_N(x) - g(x)]$, $x \in \mathcal S^*$, to which the central limit theorem applies.
--
--   **Formalization Note** This is a deterministic identity: no measurability, integrability or independence is assumed. It holds for every $N$, including the junk case $N = 0$ where both sides are $0$.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 5, §2.2, proof of Proposition 2.3, the display following "Furthermore, since v* = g(x) for any x ∈ 𝒮*"

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

namespace KleywegtSAA.ValueCLT

open MeasureTheory ProbabilityTheory Filter Topology

/-- Kleywegt–Shapiro, §2.2, p. 5: since `v* = g(x)` for every `x ∈ S*`,
`√N [min_{x ∈ S*} ĝ_N(x) − v*] = min_{x ∈ S*} {√N [ĝ_N(x) − g(x)]}`. -/
theorem sqrt_mul_minOnOpt_sub
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} (G : X → 𝒲 → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℕ → Ω → 𝒲) :
    ∀ (N : ℕ) (ω : Ω),
      Real.sqrt N * (minOnOpt S hS G P W N ω - S.inf' hS (KleywegtSAA.ExpRate.trueObj G P W)) =
        (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)).inf' (optSet_nonempty S hS (KleywegtSAA.ExpRate.trueObj G P W))
          (fun x => Real.sqrt N * (KleywegtSAA.ExpRate.sampleObj G W N ω x - KleywegtSAA.ExpRate.trueObj G P W x)) := by sorry

end KleywegtSAA.ValueCLT
