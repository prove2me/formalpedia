-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_3_3
-- name    : MartingaleHT.InfiniteServer.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:40.623412+00:00
-- url     : https://prove2.me/theorems/118345fe-1ef8-49e0-885c-15b0654c7b4d
-- title:
--   Lemma 3.3 — crude inequality $Q(t)\le Q(0)+A(\lambda t)$ and $\int_0^tQ\le t(Q(0)+A(\lambda t))$
-- statement:
--   Fix one sample path of the representation (12). Let $\lambda,\mu>0$, let $A$ be nondecreasing on $[0,\infty)$, let $S\ge0$ on $[0,\infty)$, and let $Q$ be an $\mathbb N$-valued path, integrable on every $[0,t]$, with $Q(t)=Q(0)+A(\lambda t)-S(\mu\int_0^tQ(s)\,ds)$ for all $t\ge0$. Then for all $t\ge0$,
--   $$
--   Q(t)\le Q(0)+A(\lambda t)\quad(24)\qquad\text{and}\qquad\int_0^tQ(s)\,ds\le t\,\big(Q(0)+A(\lambda t)\big)\quad(25).
--   $$
--
--   The bound gives the moment conditions (22) needed for the martingale representation and the stochastic boundedness of $\langle M_{n,2}\rangle$ in Lemma 6.2.
--
--   **Formalization Note** The lemma is pathwise; the properties of Poisson paths it uses (monotone $A$, nonnegative $S$) are stated as hypotheses on the path.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 213, Lemma 3.3, (24)–(25)

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

/-- **Lemma 3.3** (crude inequality, p. 213). Fix one sample path of the representation
(12): `λ, μ > 0`, `A` nondecreasing on `[0, ∞)`, `S ≥ 0` on `[0, ∞)`, and an `ℕ`-valued `Q`,
integrable on every `[0, t]`, with `Q(t) = Q(0) + A(λt) − S(μ ∫₀ᵗ Q(s) ds)` for all `t ≥ 0`. Then
for all `t ≥ 0`, `Q(t) ≤ Q(0) + A(λt)` (24) and `∫₀ᵗ Q(s) ds ≤ t (Q(0) + A(λt))` (25). -/
theorem lemma_3_3 (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (A S : ℝ → ℝ) (Q : ℝ → ℕ)
    (hA : MonotoneOn A (Set.Ici 0)) (hS : ∀ u : ℝ, 0 ≤ u → 0 ≤ S u)
    (hint : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => (Q s : ℝ)) volume 0 t)
    (h12 : ∀ t : ℝ, 0 ≤ t →
      (Q t : ℝ) = (Q 0 : ℝ) + A (lam * t) - S (μ * ∫ s in (0 : ℝ)..t, (Q s : ℝ))) :
    ∀ t : ℝ, 0 ≤ t → (Q t : ℝ) ≤ (Q 0 : ℝ) + A (lam * t) ∧
      ∫ s in (0 : ℝ)..t, (Q s : ℝ) ≤ t * ((Q 0 : ℝ) + A (lam * t)) := by sorry

end MartingaleHT.InfiniteServer
