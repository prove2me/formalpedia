-- Prove2me | Theorems.Thm_HighUncertHT_Game_lemma_4
-- name    : HighUncertHT.Game.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:14.333698+00:00
-- url     : https://prove2.me/theorems/59c541dc-a3bd-485a-9440-b9cdf2b9468c
-- title:
--   Lemma 4, p. 17 — snapshot principle: ‖Q̂^{ℓn} − µ^ℓŴ^{ℓn}‖_{t₀} → 0 uniformly in probability
-- statement:
--   Let $(a^n)_n$ be any sequence of admissible controls, $a^n\in\mathcal A^n$. For every $t_0>0$ and every type $\ell$,
--   $$
--   \|\hat Q^{\ell n}-\mu^\ell\hat W^{\ell n}\|_{t_0}\to0
--   $$
--   uniformly in probability as $n\to\infty$ (Definition 1, p. 16): for every $\varepsilon>0$,
--   $$
--   \sup_{\beta^n\in\mathbb B^n}\mathbb P\big(\|\hat Q^{\ell n}-\mu^\ell\hat W^{\ell n}\|_{t_0}\ge\varepsilon\big)\longrightarrow0 ,
--   $$
--   where the processes are those of the pair $(a^n,\beta^n)$.
--
--   This is a version of Reiman's snapshot principle: queue lengths and workloads are asymptotically proportional, uniformly over the scheduler's strategies.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 17, Lemma 4, with Definition 1, p. 16

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Control

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Lemma 4, p. 17 (Reiman's snapshot principle, with Definition 1, p. 16): for every sequence of
controls `aⁿ ∈ 𝒜ⁿ`, every `t₀ > 0` and every type `ℓ`, `‖Q̂^{ℓn} - µ^ℓ Ŵ^{ℓn}‖_{t₀} → 0` uniformly in
probability: for every `ε > 0`, `sup_{βⁿ ∈ 𝔹ⁿ} ℙ(‖Q̂^{ℓn} - µ^ℓ Ŵ^{ℓn}‖_{t₀} ≥ ε) → 0`. -/
theorem lemma_4 {L : ℕ} (S : Setting L) (f : (n : ℕ) → AdversaryControl S n)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (ℓ : Fin L) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => ⨆ β ∈ admissibleStrategies S n,
      (f n).law {ω | ENNReal.ofReal ε ≤ supNorm (fun s =>
        scaledQueue n ((f n).ctrlPath ω) (β ((f n).ctrlPath ω)) s ℓ -
          S.μ ℓ * scaledWorkload n ((f n).ctrlPath ω) (β ((f n).ctrlPath ω)) s ℓ) t₀})
      atTop (𝓝 0) := by sorry

end HighUncertHT.Game
