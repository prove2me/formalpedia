-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_4_1
-- name    : MartingaleHT.InfiniteServer.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:47.603743+00:00
-- url     : https://prove2.me/theorems/233e301a-6ec1-48f3-98e8-f95819c09502
-- title:
--   Lemma 4.1 — Gronwall: $0\le g(t)\le\epsilon+M\int_0^tg$ on $[0,T]$ implies $g(t)\le\epsilon e^{Mt}$
-- statement:
--   Let $g$ be a Borel-measurable real function that is integrable on $[0,T]$, and let $\epsilon>0$ and $M>0$. If
--   $$
--   0\le g(t)\le\epsilon+M\int_0^tg(s)\,ds,\qquad0\le t\le T,
--   $$
--   then
--   $$
--   g(t)\le\epsilon e^{Mt},\qquad 0\le t\le T .
--   $$
--
--   This version of Gronwall's inequality drives the continuity estimate of Theorem 4.1 and the stochastic-boundedness estimate of Lemma 5.5.
--
--   **Formalization Note** Integrability of $g$ on $[0,T]$ is added. The paper leaves it implicit; without it the statement is false when the integral is read as $+\infty$ (e.g. $g(s)=1/s$), and a Lean Bochner integral of a non-integrable function would be $0$.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 227, Lemma 4.1

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

/-- **Lemma 4.1** (version of Gronwall’s inequality, p. 227). Let `g` be Borel measurable and
integrable on `[0, T]`, and let `ε, M > 0`. If `0 ≤ g(t) ≤ ε + M ∫₀ᵗ g(s) ds` for `0 ≤ t ≤ T`,
then `g(t) ≤ ε e^{Mt}` for `0 ≤ t ≤ T`. -/
theorem lemma_4_1 (g : ℝ → ℝ) (T ε M : ℝ) (hε : 0 < ε) (hM : 0 < M)
    (hg_meas : Measurable g) (hg_int : IntegrableOn g (Set.Icc 0 T))
    (hg : ∀ t ∈ Set.Icc 0 T, 0 ≤ g t ∧ g t ≤ ε + M * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t ∈ Set.Icc 0 T, g t ≤ ε * Real.exp (M * t) := by sorry

end MartingaleHT.InfiniteServer
