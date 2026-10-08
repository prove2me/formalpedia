-- Prove2me | Theorems.Thm_MFGLimit_LDP_proposition_6_15
-- name    : MFGLimit.LDP.proposition_6_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:42.429228+00:00
-- url     : https://prove2.me/theorems/5849a859-a52e-460f-b529-bf68f1587232
-- title:
--   Proposition 6.15, pp. 31–32 — weak LDP for (Q̄^n, W) in P¹(ℝ^d × C^d_0) × C^{d₀}_0 with rate R(Q | μ₀ × 𝕎)
-- statement:
--   In the setting of §2.3, assume the initial law $\mu_0$ has exponential moments of every order (6.2). Let $\bar{\mathcal Q}^n=\frac1n\sum_{i=1}^n\delta_{(X^i_0,B^i)}$, a random element of $\mathcal P^1(\mathbb R^d\times\mathcal C^d_0)$, and let $\mathbb W$ be the Wiener measure on $\mathcal C^d_0$. Then $(\bar{\mathcal Q}^n,W)_{n\ge1}$ satisfies, on $\mathcal P^1(\mathbb R^d\times\mathcal C^d_0)\times\mathcal C^{d_0}_0$ with the metric $\max(\mathcal W_1,\|\cdot\|_\infty)$:
--
--   1. for every open $O$, $\displaystyle\liminf_{n\to\infty}\frac1n\log\mathbb P((\bar{\mathcal Q}^n,W)\in O)\ge-\inf_{(\mathcal Q,\phi)\in O}\mathcal R(\mathcal Q|\mu_0\times\mathbb W)$;
--   2. for every closed $F$,
--   $$\limsup_{n\to\infty}\frac1n\log\mathbb P((\bar{\mathcal Q}^n,W)\in F)\le-\lim_{\delta\searrow0}\inf_{(\mathcal Q,\phi)\in F_\delta}\mathcal R(\mathcal Q|\mu_0\times\mathbb W),$$
--   where $F_\delta=\{(\mathcal Q,\phi):\inf_{(\mathcal Q',\phi')\in F}\max(\mathcal W_1(\mathcal Q,\mathcal Q'),\|\phi-\phi'\|_\infty)\le\delta\}$.
--
--   This is the noise-level LDP from which Theorem 6.8 follows by contraction.
--
--   **Formalization Note** The common noise $W$ is $d_0$-dimensional, so its path lies in $\mathcal C^{d_0}_0$ (the paper writes $\mathcal C^d_0$). Condition 6.3(1) (exponential moments) is the standing assumption of §6.3.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 31–32, Proposition 6.15

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_MeasureDeriv
import Definitions.Def_MFGLimit_LDP_Equations
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_MFGLimit_LDP_PathSpace
import Definitions.Def_MFGLimit_LDP_Action
import Definitions.Def_MFGLimit_LDP_Contraction

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

/-- Proposition 6.15, pp. 31–32 (weak LDP for the pair `(Q̄^n, W)`). -/
theorem proposition_6_15 {d d₀ : ℕ} (T : ℝ≥0) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (μ₀ : Measure (MFGLimit.Conc.E d)) (hset : IsSetup 𝔽 P W B X₀ μ₀) (hexp : ExpMoments μ₀)
    (𝕎 : Measure (C0T d T)) [IsProbabilityMeasure 𝕎] (h𝕎 : IsWienerMeasure d T 𝕎) :
    LDPLower P (pairEvent W B X₀) Dqp
        (fun z : QPhi d d₀ T => InformationTheory.klDiv z.Q (μ₀.prod 𝕎)) ∧
      LDPUpperClosedDelta P (pairEvent W B X₀) Dqp
        (fun z : QPhi d d₀ T => InformationTheory.klDiv z.Q (μ₀.prod 𝕎)) := by sorry

end MFGLimit.LDP
