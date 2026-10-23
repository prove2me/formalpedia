-- Prove2me | Theorems.Thm_GameRandEnv_FirstOrder_step1_limit
-- name    : GameRandEnv.FirstOrder.step1_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:41.388791+00:00
-- url     : https://prove2.me/theorems/45aa682c-ef44-4f7d-9b70-1a030631710b
-- title:
--   §5.1 Step 1, p. 9 — (1/ε)∫₀^ε ∫ δF/δπ̄(π̄^λ, ·) d(π̄ − π̄∗) dλ → ∫ δF/δπ̄(π̄∗, ·) d(π̄ − π̄∗) by dominated convergence
-- statement:
--   Work in the setting of §2.1 (Polish environment $\mathbb Y$ with law $\mathsf m$, strategy set $\Pi$ of measures on $\bar{\mathbb R}^d=\mathbb R^d\times\mathbb Y$ with $\mathbb Y$-marginal $\mathsf m$ and finite $p$-th moment). Let $F:\Pi\to\mathbb R$ satisfy Assumption 2.1 with linear functional derivative $\frac{\delta F}{\delta\bar\pi}$. Let $\bar\pi^*,\bar\pi\in\Pi$ and put $\bar\pi^\lambda=\lambda\bar\pi+(1-\lambda)\bar\pi^*$. Then
--   $$\lim_{\varepsilon\downarrow0}\frac1\varepsilon\int_0^\varepsilon\int\frac{\delta F}{\delta\bar\pi}(\bar\pi^\lambda,\bar x)\,(\bar\pi-\bar\pi^*)(d\bar x)\,d\lambda=\int\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,\bar x)\,(\bar\pi-\bar\pi^*)(d\bar x).$$
--
--   Together with (2.1) this identifies the directional derivative of $F$ at $\bar\pi^*$ in the direction $\bar\pi-\bar\pi^*$; it is used in both halves of the proof of Theorem 3.1.
--
--   **Formalization Note** The page states this inside the necessity proof, where $\bar\pi^*$ is a minimizer of $V$ and $H(\bar\pi)<\infty$; the argument uses neither, so they are not hypotheses here. $\int g\,d(\bar\pi-\bar\pi^*)$ is written as $\int g\,d\bar\pi-\int g\,d\bar\pi^*$, and the limit is taken as $\varepsilon\to0^+$.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, p. 9, §5.1, proof of Theorem 3.1, Necessary condition, Step 1

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

open MeasureTheory Filter Topology

namespace GameRandEnv.FirstOrder

theorem step1_limit {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF)
    (πs π : Measure (Rd d × Y)) (hπs : πs ∈ Pi m p) (hπ : π ∈ Pi m p) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ t in (0 : ℝ)..ε,
        pairDiff (fun z => δF (mix t πs π) z.1 z.2) πs π)
      (𝓝[>] 0) (𝓝 (pairDiff (fun z => δF πs z.1 z.2) πs π)) := by sorry

end GameRandEnv.FirstOrder
