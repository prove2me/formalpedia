-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_theorem_4_2
-- name    : MartingaleHT.InfiniteServer.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:39.268488+00:00
-- url     : https://prove2.me/theorems/2fe3d481-c326-4882-b76a-fc2c6f21a8da
-- title:
--   Theorem 4.2 — FCLT for independent Poisson processes: $(M_{A,n},M_{S,n})\Rightarrow(B_1,B_2)$ in $D^2$
-- statement:
--   Let $A$ and $S$ be independent Poisson processes of rate $1$ on a probability space, and let
--   $$
--   M_{A,n}(t)=\frac{A(nt)-nt}{\sqrt n},\qquad M_{S,n}(t)=\frac{S(nt)-nt}{\sqrt n},\qquad t\ge0 . \tag{65}
--   $$
--   Then
--   $$
--   (M_{A,n},M_{S,n})\Rightarrow(B_1,B_2)\quad\text{in } D^2 \text{ as } n\to\infty, \tag{66}
--   $$
--   where $B_1$ and $B_2$ are independent standard Brownian motions.
--
--   This is the classical functional central limit theorem for Poisson processes, the probabilistic input of the continuous-mapping proof of Theorem 1.1.
--
--   **Formalization Note** Convergence in distribution in $D^2$ to a limit with continuous paths is stated in coupling form (`CouplingConverges`: a Skorokhod representation with almost sure uniform convergence on compact intervals), which is equivalent to $J_1$ weak convergence for continuous limits. The limit is built on some probability space in universe `Type`.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 228, Theorem 4.2, (65)–(66)

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

/-- **Theorem 4.2** (FCLT for independent Poisson processes, p. 228). If `A` and `S` are
independent rate-1 Poisson processes, then the scaled processes
`M_{A,n}(t) = (A(nt) − nt)/√n` and `M_{S,n}(t) = (S(nt) − nt)/√n` of (65) converge jointly in `D²`
to `(B₁, B₂)`, where `B₁`, `B₂` are independent standard Brownian motions. -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A S : Ω → ℝ → ℝ) (hA : IsPoissonProcess P A 1) (hS : IsPoissonProcess P S 1)
    (hAS : IndepFun (fun ω (t : ℝ≥0) => A ω t) (fun ω (t : ℝ≥0) => S ω t) P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B₁ B₂ : ℝ≥0 → Ω' → ℝ),
      IsProbabilityMeasure P' ∧ IsStandardBM P' B₁ ∧ IsStandardBM P' B₂ ∧
      IndepFun (fun ω (t : ℝ≥0) => B₁ t ω) (fun ω (t : ℝ≥0) => B₂ t ω) P' ∧
      CouplingConverges P P'
        (fun n ω t => ![scaledPoisson n A ω t, scaledPoisson n S ω t])
        (fun ω t => ![B₁ t.toNNReal ω, B₂ t.toNNReal ω]) := by sorry

end MartingaleHT.InfiniteServer
