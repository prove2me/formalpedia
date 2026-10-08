-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_3_2
-- name    : MartingaleHT.InfiniteServer.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:57.206681+00:00
-- url     : https://prove2.me/theorems/7d66d70d-6697-4165-971d-a141a11e22eb
-- title:
--   Lemma 3.2 — random time change $S\circ I$ of a rate-1 Poisson process: $S\circ I-I$ is an $\mathbf F_I$-martingale with $\langle M\rangle=I$
-- statement:
--   Let $\mathbf F=(\mathcal F_t)_{t\ge0}$ be a filtration and $S$ a rate-$1$ Poisson process that is adapted to $\mathbf F$ and such that $S(t)-t$ is an $\mathbf F$-martingale. Let $I=(I(t))_{t\ge0}$ have continuous nondecreasing nonnegative paths with $I(0)=0$, where each $I(t)$ is an $\mathbf F$-stopping time, and assume
--   $$
--   E[I(t)]<\infty\quad\text{and}\quad E[S(I(t))]<\infty\qquad\text{for all } t\ge0. \tag{22}
--   $$
--   Then $S\circ I$ is a non-explosive unit-jump counting process, and $M=S\circ I-I$ is a square-integrable martingale with respect to $\mathbf F_I=(\mathcal F_{I(t)})_{t\ge0}$, the filtration of the stopped $\sigma$-algebras, with predictable quadratic variation $\langle M\rangle(t)=I(t)$.
--
--   The lemma is what turns the departure process $S(\mu\int_0^tQ(s)\,ds)$ of the queue into a martingale plus its compensator.
--
--   **Formalization Note** Two hypotheses are added. (a) $S(t)-t$ is an $\mathbf F$-martingale: the printed "rate-1 Poisson process adapted to $\mathbf F$" does not exclude a filtration that knows the future of $S$, and the proof uses exactly this martingale property (p. 214). (b) $I(0)=0$: a counting process starts at $0$ (§3.3), and $S(I(0))\ne0$ is possible otherwise. The optional quadratic variation $[M](t)=S(I(t))$ in (23) is not formalized.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 212, Lemma 3.2, (22)–(23) (the ⟨M⟩ part)

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

/-- **Lemma 3.2** (random time change of a rate-1 Poisson process, p. 212), predictable part.
Let `S` be a rate-1 Poisson process that is an `𝓕`-Poisson process (adapted, with `S(t) − t` an
`𝓕`-martingale), and let `I` have continuous nondecreasing paths with `I(0) = 0`, each `I(t)`
an `𝓕`-stopping time, with `E[I(t)] < ∞` and `E[S(I(t))] < ∞` for all `t ≥ 0` (22). Then
`S ∘ I` is a non-explosive unit-jump counting process and `M = S ∘ I − I` is a
square-integrable martingale with respect to `𝓕_I = (𝓕_{I(t)})`, with `⟨M⟩ = I`. -/
theorem lemma_3_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (S : Ω → ℝ → ℝ) (hS : IsPoissonProcess P S 1)
    (hSad : ∀ t : ℝ≥0, StronglyMeasurable[𝓕 t] (fun ω => S ω t))
    (hSF : Martingale (fun (t : ℝ≥0) ω => S ω t - t) 𝓕 P)
    (I : ℝ≥0 → Ω → ℝ≥0) (hIcont : ∀ ω, Continuous (fun t => I t ω))
    (hImono : ∀ ω, Monotone (fun t => I t ω)) (hI0 : ∀ ω, I 0 ω = 0)
    (hIst : ∀ t, IsStoppingTime 𝓕 (fun ω => ((I t ω : ℝ≥0) : WithTop ℝ≥0)))
    (h22 : ∀ t, Integrable (fun ω => (I t ω : ℝ)) P ∧ Integrable (fun ω => S ω (I t ω)) P) :
    (∀ᵐ ω ∂P, IsUnitJumpCountingPath (fun t => S ω (I t ω))) ∧
    IsPQV (fun t => (hIst t).measurableSpace) P (fun t ω => S ω (I t ω) - I t ω)
      (fun t ω => I t ω) := by sorry

end MartingaleHT.InfiniteServer
