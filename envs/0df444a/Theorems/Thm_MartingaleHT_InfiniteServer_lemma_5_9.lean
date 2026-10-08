-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_5_9
-- name    : MartingaleHT.InfiniteServer.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:06.6389+00:00
-- url     : https://prove2.me/theorems/d7d2da54-4338-4eb4-aa1d-b1dc2032b14a
-- title:
--   Lemma 5.9 — FWLLN from stochastic boundedness: $X_n$ SB in $D^k$ and $a_n\to\infty$ imply $X_n/a_n\Rightarrow0$
-- statement:
--   Let $X_n$, $n\ge1$, be random elements of $D^k$ (processes with values in $\mathbb R^k$, paths right-continuous with left limits, measurable coordinates) and let $a_n>0$ with $a_n\to\infty$. If $(X_n)$ is stochastically bounded in $D^k$, then
--   $$
--   \frac{X_n}{a_n}\Rightarrow\eta\quad\text{in }D^k\text{ as }n\to\infty, \tag{82}
--   $$
--   where $\eta(t)=(0,\dots,0)$ for $t\ge0$.
--
--   With $a_n=\sqrt n$ it turns stochastic boundedness of the diffusion-scaled queue into the fluid limit of Lemma 4.3.
--
--   **Formalization Note** Convergence in distribution to the deterministic continuous limit $\eta$ is convergence in probability (p. 229), stated as uniform convergence on compact time intervals in probability (`UocInProb`).
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 238, Lemma 5.9, (82)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MartingaleHT.InfiniteServer

open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling ErlangA.Diffusion

/-- **Lemma 5.9** (FWLLN from stochastic boundedness in `Dᵏ`, p. 238). Let `Xₙ` be random
elements of `Dᵏ` and `aₙ > 0` with `aₙ → ∞`. If `(Xₙ)` is stochastically bounded in `Dᵏ`, then
`Xₙ/aₙ ⇒ η` in `Dᵏ`, where `η ≡ 0`; since the limit is deterministic and continuous this is
uniform convergence on compact time intervals in probability. -/
theorem lemma_5_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (hcad : ∀ n : ℕ, 1 ≤ n → ∀ ω i, IsCadlag (fun t => X n ω t i))
    (hmeas : ∀ n : ℕ, 1 ≤ n → ∀ t, Measurable (fun ω => X n ω t))
    (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hlim : Tendsto a atTop atTop)
    (hSB : IsSBD P X) :
    UocInProb P (fun n ω t => (a n)⁻¹ • X n ω t) (fun _ => 0) := by sorry

end MartingaleHT.InfiniteServer
