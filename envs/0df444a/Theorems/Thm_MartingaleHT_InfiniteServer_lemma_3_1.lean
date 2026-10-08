-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_3_1
-- name    : MartingaleHT.InfiniteServer.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:45.457656+00:00
-- url     : https://prove2.me/theorems/5231b143-e92d-4773-bebd-f7132f71b8ef
-- title:
--   Lemma 3.1 — a unit-jump counting process with continuous compensator $A$: $M=N-A$ is square integrable with $\langle M\rangle=A$
-- statement:
--   Let $\mathbf F=(\mathcal F_t)_{t\ge0}$ be a filtration on a probability space and let $N$ be a non-explosive unit-jump counting process adapted to $\mathbf F$ with $E[N(t)]<\infty$ for all $t$. Let $A$ be its compensator, that is an adapted process with nondecreasing paths, $A(0)=0$ and $E[A(t)]<\infty$, such that $N-A$ is an $\mathbf F$-martingale, and assume $A$ has continuous paths. Then $M=N-A$ is a square-integrable $\mathbf F$-martingale and its predictable quadratic variation is
--   $$
--   \langle M\rangle=A,
--   $$
--   i.e. $M^2-A$ is an $\mathbf F$-martingale.
--
--   This identifies the quadratic variations of the compensated Poisson processes in the queueing representations.
--
--   **Formalization Note** The compensator is the one of the Doob–Meyer decomposition (Theorem 3.1), normalized by $A(0)=0$. "Unit-jump counting" (§3.3: $N(0)=0$, $\mathbb N$-valued, nondecreasing, right-continuous, jumps of size $1$) is required of almost every path. The optional quadratic variation $[M]=N$ in the same sentence of the lemma is not formalized.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 211, Lemma 3.1 (the ⟨M⟩ = A part)

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

/-- **Lemma 3.1** (PQV for unit-jump counting processes, p. 211), predictable part. Let `N`
be a non-explosive unit-jump counting process adapted to a filtration `𝓕` with `E[N(t)] < ∞` for
all `t`, and let its compensator `Λ` (an adapted process with nondecreasing paths, `Λ(0) = 0`,
`E[Λ(t)] < ∞`, such that `N − Λ` is an `𝓕`-martingale) be continuous. Then `M = N − Λ` is a
square-integrable `𝓕`-martingale with predictable quadratic variation `⟨M⟩ = Λ`. -/
theorem lemma_3_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (N Λ : ℝ≥0 → Ω → ℝ)
    (hN : ∀ᵐ ω ∂P, IsUnitJumpCountingPath (fun t => N t ω))
    (hNad : ∀ t, StronglyMeasurable[𝓕 t] (N t)) (hNint : ∀ t, Integrable (N t) P)
    (hΛad : ∀ t, StronglyMeasurable[𝓕 t] (Λ t)) (hΛcont : ∀ ω, Continuous (fun t => Λ t ω))
    (hΛmono : ∀ ω, Monotone (fun t => Λ t ω)) (hΛ0 : ∀ ω, Λ 0 ω = 0)
    (hΛint : ∀ t, Integrable (Λ t) P)
    (hcomp : Martingale (fun t ω => N t ω - Λ t ω) 𝓕 P) :
    IsPQV (fun t => 𝓕 t) P (fun t ω => N t ω - Λ t ω) Λ := by sorry

end MartingaleHT.InfiniteServer
