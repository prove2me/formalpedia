-- Prove2me | Theorems.Thm_NonstatNV_lemma_4
-- name    : NonstatNV.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:50.474829+00:00
-- url     : https://prove2.me/theorems/2db03332-ad90-4706-8595-60a6971c67de
-- title:
--   Lemma 4 — the drift of the window average is at most $C_2T^{(3+v)/4}$
-- statement:
--   Fix a scaling constant $\kappa>0$. There is a constant $C_2\in(0,\infty)$, depending only on $\kappa$, such that for every horizon $T\ge1$, every $v\in[0,1]$ and every sequence of means $\mu$ with demand variation $V_\mu\le T^v$, writing $n=\lceil\kappa T^{(1-v)/2}\rceil$,
--
--   $$
--   \sum_{t=n+1}^{T}\left|\frac1n\sum_{s=t-n}^{t-1}(\mu_s-\mu_t)\right|\le C_2\,T^{(3+v)/4}.
--   $$
--
--   It bounds the bias of the window average caused by drifting means, the deterministic half of the estimation error of the Fixed-Time-Window Policy.
--
--   Differences from the source:
--   - reading: there exists a universal constant C₂ → C₂ depends only on κ and is chosen before T, v and μ; reason: the proof's value is √κ; universal means independent of T, v and the instance
--   - encoding: n (Algorithm 1: n = ⌈κT^{(1−v)/2}⌉; the proof ignores the rounding) → n = ⌈κT^{(1−v)/2}⌉ with the ceiling; reason: the window size of the algorithm; the existential constant absorbs the rounding
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Lemma 4, p.36 (proof pp.36–37)

import Definitions.Def_NonstatNV_demandVariation
import Definitions.Def_NonstatNV_windowSize

namespace NonstatNV

/-- **Lemma 4** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.36; proof pp.36–37). There is a constant `C₂ ∈ (0, ∞)` such that, with
`n = ⌈κT^{(1−v)/2}⌉`,
`Σ_{t=n+1}^{T} |(1/n) Σ_{s=t−n}^{t−1} (μ_s − μ_t)| ≤ C₂ T^{(3+v)/4}`
for every horizon `T ≥ 1`, every `v ∈ [0, 1]` and every sequence of means with `V_μ ≤ T^v`.

**Formalization Note** `C₂` depends on the scaling constant `κ > 0` only (the proof's value is
`√κ`, computed with the ceiling ignored); it is chosen before `T`, `v` and `μ`. The ceiling in
`n` is kept. -/
theorem lemma_4 (κ : ℝ) (hκ : 0 < κ) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ T : ℕ, 1 ≤ T → ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ μ : ℕ → ℝ,
      demandVariation μ T ≤ (T : ℝ) ^ v →
        ∑ t ∈ Finset.Icc (windowSize T v κ + 1) T,
            |(1 / (windowSize T v κ : ℝ)) *
              ∑ s ∈ Finset.Ico (t - windowSize T v κ) t, (μ s - μ t)| ≤
          C₂ * (T : ℝ) ^ ((3 + v) / 4) := by sorry

end NonstatNV
