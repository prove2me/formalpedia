-- Prove2me | Theorems.Thm_HighUncertHT_Game_lemma_5
-- name    : HighUncertHT.Game.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:06.390988+00:00
-- url     : https://prove2.me/theorems/6a7ce719-ed22-4be9-aadd-eb98e8269d00
-- title:
--   Lemma 5, p. 17 — under β*ⁿ the workload concentrates on type 1: Σ_{ℓ≥2} Ŵ^{ℓn} → 0
-- statement:
--   Assume that the scheduler applies the nonpreemptive cµ strategy $\beta^{*n}$. Then for every sequence of admissible controls $a^n\in\mathcal A^n$,
--   $$
--   \sum_{\ell=2}^L\hat W^{\ell n}\to0\quad\text{in probability as }n\to\infty,
--   $$
--   in the sense that for every $t_0>0$ and $\varepsilon>0$, $\mathbb P\big(\|\sum_{\ell=2}^L\hat W^{\ell n}\|_{t_0}>\varepsilon\big)\to0$.
--
--   Under the priority rule the workload of the high-priority types $2,\dots,L$ is negligible on the diffusion scale, so the total workload is asymptotically held by the lowest-priority type 1, the one with the smallest holding cost rate $h^1\mu^1$.
--
--   **Formalization Note** "→ 0 in probability" for processes is read as convergence of the sup norm on every compact interval $[0,t_0]$, which is what the proof establishes. Types $2,\dots,L$ are the 0-based indices other than `S.first`.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 17, Lemma 5

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Control
import Definitions.Def_HighUncertHT_Game_Priority

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Lemma 5, p. 17: under the nonpreemptive cµ strategy `β^{*n}`, for every sequence of controls
`aⁿ ∈ 𝒜ⁿ`, `Σ_{ℓ=2}^L Ŵ^{ℓn} → 0` in probability: for every `t₀ > 0` and `ε > 0`,
`ℙ(‖Σ_{ℓ=2}^L Ŵ^{ℓn}‖_{t₀} > ε) → 0`. (The paper's types `2, …, L` are the Lean indices other than
`S.first = 0`.) -/
theorem lemma_5 {L : ℕ} (S : Setting L) (f : (n : ℕ) → AdversaryControl S n)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (f n).law {ω | ENNReal.ofReal ε < supNorm (fun s =>
        ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ S.first),
          scaledWorkload n ((f n).ctrlPath ω) (betaStar S n ((f n).ctrlPath ω)) s ℓ) t₀})
      atTop (𝓝 0) := by sorry

end HighUncertHT.Game
