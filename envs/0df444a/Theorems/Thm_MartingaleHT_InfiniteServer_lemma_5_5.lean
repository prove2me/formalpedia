-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_5_5
-- name    : MartingaleHT.InfiniteServer.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:52.187963+00:00
-- url     : https://prove2.me/theorems/bff2acb9-ae31-4144-aeb7-b881d97ec40b
-- title:
--   Lemma 5.5 — stochastic boundedness for integral representations $X_n=X_n(0)+\sum_iY_{n,i}+\int_0^\cdot h(X_n)$
-- statement:
--   Let $h$ be Lipschitz as in (62) (there is $c>0$ with $|h(s_1)-h(s_2)|\le c|s_1-s_2|$), fix $k$, and for each $n\ge1$ let $X_n$ and $Y_{n,1},\dots,Y_{n,k}$ be real processes with paths in $D$ and measurable coordinates such that, almost surely,
--   $$
--   X_n(t)=X_n(0)+Y_{n,1}(t)+\cdots+Y_{n,k}(t)+\int_0^th(X_n(s))\,ds,\qquad t\ge0 .
--   $$
--   If $\{X_n(0):n\ge1\}$ is stochastically bounded in $\mathbb R$ and $\{Y_{n,i}:n\ge1\}$ is stochastically bounded in $D$ for each $1\le i\le k$, then $\{X_n:n\ge1\}$ is stochastically bounded in $D$.
--
--   Applied to the representation (32) with $h(s)=-\mu s$, it reduces stochastic boundedness of $X_n$ to that of the initial values and of the martingales.
--
--   **Formalization Note** $h(0)=0$ is not assumed, as in the paper. The representation is required almost surely.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 236, Lemma 5.5

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

/-- **Lemma 5.5** (stochastic boundedness for integral representations, p. 236). Let `h` be
Lipschitz as in (62) and, for each `n ≥ 1`, let `Xₙ`, `Yₙ,₁, …, Yₙ,ₖ` be processes with paths in
`D` and measurable coordinates such that, almost surely, for all `t ≥ 0`,
`Xₙ(t) = Xₙ(0) + Yₙ,₁(t) + ⋯ + Yₙ,ₖ(t) + ∫₀ᵗ h(Xₙ(s)) ds`. If `(Xₙ(0))` is stochastically bounded
in `ℝ` and each `(Yₙ,ᵢ)` is stochastically bounded in `D`, then `(Xₙ)` is stochastically bounded
in `D`. -/
theorem lemma_5_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|)
    (X : ℕ → Ω → ℝ → ℝ) (Y : ℕ → Fin k → Ω → ℝ → ℝ)
    (hXcad : ∀ n : ℕ, 1 ≤ n → ∀ ω, IsCadlag (X n ω))
    (hYcad : ∀ n : ℕ, 1 ≤ n → ∀ i ω, IsCadlag (Y n i ω))
    (hXmeas : ∀ n : ℕ, 1 ≤ n → ∀ t, Measurable (fun ω => X n ω t))
    (hYmeas : ∀ n : ℕ, 1 ≤ n → ∀ i t, Measurable (fun ω => Y n i ω t))
    (hrep : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      X n ω t = X n ω 0 + ∑ i, Y n i ω t + ∫ s in (0 : ℝ)..t, h (X n ω s))
    (hX0 : IsSBReal P (fun n ω => X n ω 0))
    (hY : ∀ i, IsSBD P (fun n ω t (_ : Fin 1) => Y n i ω t)) :
    IsSBD P (fun n ω t (_ : Fin 1) => X n ω t) := by sorry

end MartingaleHT.InfiniteServer
