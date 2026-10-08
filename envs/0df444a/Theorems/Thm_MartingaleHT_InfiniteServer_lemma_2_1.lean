-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_2_1
-- name    : MartingaleHT.InfiniteServer.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:41.27797+00:00
-- url     : https://prove2.me/theorems/1c2bc9ec-b077-4dae-a355-baa034467cab
-- title:
--   Lemma 2.1 — formula (12) defines the $M/M/\infty$ queue $Q$ as a random element of $D$
-- statement:
--   Let $A$ and $S$ be Poisson processes of rate $1$ and $Q_0$ an $\mathbb N$-valued random variable on a probability space $(\Omega,\mathcal F,P)$, mutually independent, and let $\lambda,\mu>0$. Then there is a process $Q$ with $Q(0)=Q_0$, values in $\mathbb N$, right-continuous paths with left limits and measurable coordinates such that, almost surely, for all $t\ge0$,
--   $$
--   Q(t)=Q(0)+A(\lambda t)-S\Big(\mu\int_0^tQ(s)\,ds\Big). \tag{12}
--   $$
--   Moreover any two such processes with the same initial value $Q_0$ agree, almost surely, at every $t\ge0$.
--
--   This is what makes the $M/M/\infty$ model of the mission well defined: the departure process inside (12) depends on the history of $Q$ itself, so existence and uniqueness are not obvious.
--
--   **Formalization Note** Only the first sentence of Lemma 2.1 is formalized ("well defined as a random element of $D$"). The second sentence, that $Q$ is a birth-and-death process with rates $\lambda_k=\lambda$ and $\mu_k=k\mu$, needs a generator or transition-rate formalism and is not stated.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 202, Lemma 2.1 (first sentence)

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

/-- **Lemma 2.1** (construction, p. 202), first sentence. Let `A`, `S` be rate-1 Poisson
processes and `Q₀` an `ℕ`-valued random variable, mutually independent, on a probability space
`(Ω, P)`, and let `λ, μ > 0`. Then formula (12), `Q(t) = Q(0) + A(λt) − S(μ ∫₀ᵗ Q(s) ds)`,
defines `Q` as a random element of `D`: there is an `ℕ`-valued process `Q` with `Q(0) = Q₀`,
right-continuous paths with left limits and measurable coordinates that satisfies (12) almost
surely for all `t ≥ 0` (an `M/M/∞` system), and any two such processes are indistinguishable on
`[0, ∞)`. -/
theorem lemma_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (A S : Ω → ℝ → ℝ) (hA : IsPoissonProcess P A 1) (hS : IsPoissonProcess P S 1)
    (Q₀ : Ω → ℕ) (hQ₀ : Measurable Q₀)
    (hind : iIndepFun (![fun ω (t : ℝ≥0) => A ω t, fun ω (t : ℝ≥0) => S ω t,
      fun ω (_ : ℝ≥0) => (Q₀ ω : ℝ)] : Fin 3 → Ω → ℝ≥0 → ℝ) P) :
    (∃ Q : Ω → ℝ → ℕ, IsMMInfSystem P lam μ A S Q ∧ ∀ ω, Q ω 0 = Q₀ ω) ∧
    ∀ Q₁ Q₂ : Ω → ℝ → ℕ, IsMMInfSystem P lam μ A S Q₁ → IsMMInfSystem P lam μ A S Q₂ →
      (∀ ω, Q₁ ω 0 = Q₀ ω) → (∀ ω, Q₂ ω 0 = Q₀ ω) →
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Q₁ ω t = Q₂ ω t := by sorry

end MartingaleHT.InfiniteServer
