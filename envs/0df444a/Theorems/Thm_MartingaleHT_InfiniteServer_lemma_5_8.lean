-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_5_8
-- name    : MartingaleHT.InfiniteServer.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:43.598422+00:00
-- url     : https://prove2.me/theorems/d8d81cf2-85fe-4165-999c-e2ee0b29c333
-- title:
--   Lemma 5.8 — SB criterion for square-integrable martingales: $\langle M_n\rangle(T)$ SB for each $T$ implies $M_n$ SB in $D$
-- statement:
--   For each $n\ge1$ let $M_n$ be a square-integrable martingale with paths in $D$ with respect to a filtration $\mathcal G_n$, with $M_n(0)=0$ almost surely, and let $\langle M_n\rangle$ be its predictable quadratic variation, so that $M_n^2-\langle M_n\rangle$ is a martingale. If the random variables $\{\langle M_n\rangle(T):n\ge1\}$ are stochastically bounded in $\mathbb R$ for each $T>0$, then the processes $\{M_n:n\ge1\}$ are stochastically bounded in $D$:
--   $$
--   \forall T>0\ \forall\varepsilon>0\ \exists c\ \forall n\ge1:\quad P\Big(\sup_{0\le t\le T}|M_n(t)|>c\Big)\le\varepsilon .
--   $$
--
--   This criterion moves stochastic boundedness from the quadratic variations to the martingales $M_{n,1}$, $M_{n,2}$.
--
--   **Formalization Note** The hypothesis $M_n(0)=0$ is added. As printed the lemma is false: $M_n\equiv n$ is a square-integrable martingale with $\langle M_n\rangle\equiv0$, which is stochastically bounded, while $(M_n)$ is not stochastically bounded in $D$. The Lenglart–Rebolledo inequality (81) used in the proof needs $M(0)=0$, and both applications ($M_{n,1}$, $M_{n,2}$) satisfy it.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 238, Lemma 5.8 (with M_n(0) = 0, see note)

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

/-- **Lemma 5.8** (SB criterion for square-integrable martingales, p. 238), with the
hypothesis `Mₙ(0) = 0` that its proof (Lenglart–Rebolledo) needs. For each `n ≥ 1` let `Mₙ` be a
square-integrable martingale with paths in `D`, `Mₙ(0) = 0` a.s., with respect to its own
filtration `𝓖ₙ`, with predictable quadratic variation `⟨Mₙ⟩ = Vₙ`. If `(Vₙ(T))` is
stochastically bounded in `ℝ` for each `T > 0`, then `(Mₙ)` is stochastically bounded in `D`. -/
theorem lemma_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : ℕ → ℝ≥0 → MeasurableSpace Ω) (M V : ℕ → ℝ≥0 → Ω → ℝ)
    (hPQV : ∀ n : ℕ, 1 ≤ n → IsPQV (𝓖 n) P (M n) (V n))
    (hcad : ∀ n : ℕ, 1 ≤ n → ∀ ω, IsCadlag (fun t : ℝ => M n t.toNNReal ω))
    (hM0 : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, M n 0 ω = 0)
    (hV : ∀ T : ℝ, 0 < T → IsSBReal P (fun n ω => V n T.toNNReal ω)) :
    IsSBD P (fun n ω (t : ℝ) (_ : Fin 1) => M n t.toNNReal ω) := by sorry

end MartingaleHT.InfiniteServer
