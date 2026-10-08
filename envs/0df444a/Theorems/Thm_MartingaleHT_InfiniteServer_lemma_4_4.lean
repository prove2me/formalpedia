-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_4_4
-- name    : MartingaleHT.InfiniteServer.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:12.115814+00:00
-- url     : https://prove2.me/theorems/019181f4-6edb-4164-85f4-f3f029e1e59f
-- title:
--   Lemma 4.4 — all but the fluid limit: if $Q_n/n\Rightarrow1$ then $(M_{n,1},M_{n,2})\Rightarrow(\sqrt\mu B_1,\sqrt\mu B_2)$ in $D^2$
-- statement:
--   Fix $\mu>0$ and, for every $n\ge1$, an $M/M/\infty$ system $Q_n$ with arrival rate $\lambda_n=n\mu$ and service rate $\mu$, built from its own unit-rate Poisson processes $A_n,S_n$ as in (12), all on one probability space. Let $M_{n,1}(t)=(A_n(\lambda_nt)-\lambda_nt)/\sqrt n$ and $M_{n,2}(t)=\big(S_n(\mu\int_0^tQ_n)-\mu\int_0^tQ_n\big)/\sqrt n$ be the scaled martingales (29)–(30). If the fluid limit (70) holds, i.e. $Q_n/n\Rightarrow1$ in $D$, then
--   $$
--   (M_{n,1},M_{n,2})\Rightarrow(\sqrt\mu B_1,\sqrt\mu B_2)\quad\text{in }D^2, \tag{72}
--   $$
--   where $B_1$ and $B_2$ are independent standard Brownian motions.
--
--   With Theorems 3.4 and 4.1 this gives Theorem 1.1, once the fluid limit is established.
--
--   **Formalization Note** The hypothesis (70) is uniform convergence on compact intervals in probability, the limit (72) is in coupling form (`CouplingConverges`), equivalent to $J_1$ weak convergence for continuous limits. The words "as required to complete the proof of Theorem 1.1" are commentary and are not formalized. The initial condition (4) is not assumed, as in the paper.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 229, Lemma 4.4, (72)

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

open BellWilliams2001.ThresholdPolicy ErlangA.Diffusion

/-- **Lemma 4.4** (all but the fluid limit, p. 229). For the sequence of `M/M/∞` systems of
Theorem 1.1 (`μ > 0`, `λₙ = nμ`), if the fluid limit (70) holds, i.e. `Qₙ/n` converges to the
constant path `1` uniformly on compact intervals in probability, then the scaled martingales
`(M_{n,1}, M_{n,2})` of (29)–(30) converge in `D²` to `(√μ B₁, √μ B₂)`, where `B₁`, `B₂` are
independent standard Brownian motions. -/
theorem lemma_4_4 (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (h70 : UocInProb P (fun n ω t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B₁ B₂ : ℝ≥0 → Ω' → ℝ),
      IsProbabilityMeasure P' ∧ IsStandardBM P' B₁ ∧ IsStandardBM P' B₂ ∧
      IndepFun (fun ω (t : ℝ≥0) => B₁ t ω) (fun ω (t : ℝ≥0) => B₂ t ω) P' ∧
      CouplingConverges P P'
        (fun n ω t => ![scaledM1 n (n * μ) (A n) ω t, scaledM2 n μ (S n) (Q n) ω t])
        (fun ω t => ![Real.sqrt μ * B₁ t.toNNReal ω, Real.sqrt μ * B₂ t.toNNReal ω]) := by sorry

end MartingaleHT.InfiniteServer
