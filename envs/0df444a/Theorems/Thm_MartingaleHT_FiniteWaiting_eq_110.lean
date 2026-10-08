-- Prove2me | Theorems.Thm_MartingaleHT_FiniteWaiting_eq_110
-- name    : MartingaleHT.FiniteWaiting.eq_110
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:16.526981+00:00
-- url     : https://prove2.me/theorems/3857ed95-2cc0-4ef4-b84a-1294352dc71e
-- title:
--   §7.1, (110) — $B_1\circ\mu e-B_2\circ\mu e-B_3\circ\eta$ has the law of $\sqrt{2\mu}\,B$
-- statement:
--   Let $\mu>0$, let $B_1,B_2,B_3$ be independent standard Brownian motions on a probability space $(\Omega,P)$, and let $B$ be a standard Brownian motion on a probability space $(\Omega'',P'')$. Write $e(t)=t$ for the identity map and $\eta(t)\equiv0$ for the zero function. Then, as processes indexed by $t\ge0$,
--   $$
--   B_1\circ\mu e-B_2\circ\mu e-B_3\circ\eta\ \overset{d}{=}\ B_1\circ\mu e-B_2\circ\mu e-\eta\ \overset{d}{=}\ \sqrt{2\mu}\,B,
--   $$
--   that is, the three processes $t\mapsto B_1(\mu t)-B_2(\mu t)-B_3(0)$, $t\mapsto B_1(\mu t)-B_2(\mu t)$ and $t\mapsto\sqrt{2\mu}\,B(t)$ have the same law on path space.
--
--   This identifies the noise in the heavy-traffic limit: the arrival and service noise combine into a Brownian motion with variance $2\mu$, and the abandonment noise vanishes because its time change converges to zero.
--
--   **Formalization Note** The display (110) appears in the proof of Theorem 7.1 (§7.1); the proof of Theorem 1.2 invokes it through "The proof can be much the same as in §7.1" (p. 250). Equality in law is `IdentDistrib` of the paths indexed by $\mathbb R_{\ge0}$ (product σ-algebra). $\mu e$ is realized as $t\mapsto \mu t$ in $\mathbb R_{\ge0}$. Brownian motion is `ErlangA.Diffusion.IsStandardBM`.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 250, §7.1, (110)

import Mathlib
import Definitions.Def_ErlangA_Diffusion_SDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MartingaleHT.FiniteWaiting

open ErlangA.Diffusion

/-- **§7.1, (110)** (p. 250). Let `µ > 0`, let `B₁`, `B₂`, `B₃` be independent standard Brownian
motions on `(Ω, P)`, and let `B` be a standard Brownian motion on `(Ω'', P'')`. With `e(t) = t`
and `η(t) ≡ 0`,
`B₁ ∘ µe − B₂ ∘ µe − B₃ ∘ η =ᵈ B₁ ∘ µe − B₂ ∘ µe − η =ᵈ √(2µ) B`
as processes indexed by `t ≥ 0` (equality of laws on path space). -/
theorem eq_110 (μ : ℝ) (hμ : 0 < μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B₁ B₂ B₃ : ℝ≥0 → Ω → ℝ)
    (h₁ : IsStandardBM P B₁) (h₂ : IsStandardBM P B₂) (h₃ : IsStandardBM P B₃)
    (hind : iIndepFun (![fun ω (t : ℝ≥0) => B₁ t ω, fun ω (t : ℝ≥0) => B₂ t ω,
      fun ω (t : ℝ≥0) => B₃ t ω] : Fin 3 → Ω → ℝ≥0 → ℝ) P)
    {Ω'' : Type*} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (B : ℝ≥0 → Ω'' → ℝ) (hB : IsStandardBM P'' B) :
    IdentDistrib (fun ω (t : ℝ≥0) => B₁ (μ.toNNReal * t) ω - B₂ (μ.toNNReal * t) ω - B₃ 0 ω)
      (fun ω (t : ℝ≥0) => B₁ (μ.toNNReal * t) ω - B₂ (μ.toNNReal * t) ω - 0) P P ∧
    IdentDistrib (fun ω (t : ℝ≥0) => B₁ (μ.toNNReal * t) ω - B₂ (μ.toNNReal * t) ω - 0)
      (fun ω (t : ℝ≥0) => Real.sqrt (2 * μ) * B t ω) P P'' := by sorry

end MartingaleHT.FiniteWaiting
