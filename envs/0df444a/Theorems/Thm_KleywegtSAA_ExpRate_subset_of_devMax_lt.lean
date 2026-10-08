-- Prove2me | Theorems.Thm_KleywegtSAA_ExpRate_subset_of_devMax_lt
-- name    : KleywegtSAA.ExpRate.subset_of_devMax_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:59.789045+00:00
-- url     : https://prove2.me/theorems/4bbdd98c-a0dd-40a5-9e9e-24ba282e4ea3
-- title:
--   §2.1, proof of Proposition 2.1, p. 3 — if δ_N < α(ε)/2 then Ŝ^ε_N ⊂ 𝒮^ε
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $g$ the true objective and $\hat g_N$ the sample average function along a realization $\omega$, $\varepsilon \ge 0$, and suppose $\mathcal S \setminus \mathcal S^\varepsilon$ is nonempty so that $\alpha(\varepsilon)$ of (2.3) is defined. For every sample size $N$ and every realization $\omega$,
--   $$\delta_N = \max_{x \in \mathcal S} |\hat g_N(x) - g(x)| < \frac{\alpha(\varepsilon)}{2} \quad\Longrightarrow\quad \hat{\mathcal S}^\varepsilon_N \subset \mathcal S^\varepsilon.$$
--
--   This is the deterministic core of Propositions 2.1 and 2.2: once the sample average is uniformly within $\alpha(\varepsilon)/2$ of the true objective, every $\varepsilon$-optimal solution of the SAA problem is $\varepsilon$-optimal for the true problem.
--
--   **Formalization Note** The implication is pointwise in $\omega$ and $N$; it needs no independence, integrability or measurability, so those standing hypotheses are omitted (a stronger statement).
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 3, proof of Proposition 2.1 (restated p. 4, §2.2)

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace KleywegtSAA.ExpRate

/-- Proof of Proposition 2.1, p. 3 (restated p. 4): if `δ_N < α(ε)/2` then `Ŝ^ε_N ⊂ S^ε`.
Deterministic in the realization `ω` and the sample size `N`. -/
theorem subset_of_devMax_lt {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} (G : X → 𝒲 → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℕ → Ω → 𝒲)
    (ε : ℝ) (hε : 0 ≤ ε) (hne : (nonOptSet S hS (trueObj G P W) ε).Nonempty) :
    ∀ (N : ℕ) (ω : Ω), devMax S hS G P W N ω < alpha S hS (trueObj G P W) ε hne / 2 →
      epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε := by sorry

end KleywegtSAA.ExpRate
