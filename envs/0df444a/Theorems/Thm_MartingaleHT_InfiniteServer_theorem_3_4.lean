-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_theorem_3_4
-- name    : MartingaleHT.InfiniteServer.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:02.525997+00:00
-- url     : https://prove2.me/theorems/f48945cf-2a26-46f2-9b67-3093cab604da
-- title:
--   Theorem 3.4 — first martingale representation $X_n=X_n(0)+M_{n,1}-M_{n,2}-\mu\int_0^\cdot X_n$, with $\langle M_{n,1}\rangle=\lambda_nt/n$, $\langle M_{n,2}\rangle=\frac{\mu}{n}\int_0^tQ_n$
-- statement:
--   Fix $\mu>0$ and, for every $n\ge1$, an $M/M/\infty$ system $Q_n$ with arrival rate $\lambda_n=n\mu$ and service rate $\mu$ built from unit-rate Poisson processes $A_n,S_n$ as in (12), all on one probability space, with $E[Q_n(0)]<\infty$. Let $X_n(t)=(Q_n(t)-n)/\sqrt n$ and let $M_{n,1}$, $M_{n,2}$ be the scaled martingales of (29)–(30). Then, for each $n\ge1$:
--
--   1. almost surely, for all $t\ge0$,
--   $$
--   X_n(t)=X_n(0)+M_{n,1}(t)-M_{n,2}(t)-\mu\int_0^tX_n(s)\,ds ; \tag{32}
--   $$
--   2. $M_{n,1}$ and $M_{n,2}$ are square-integrable martingales with respect to the filtration $\mathcal F_{n,t}=\sigma\big(Q_n(0),A_n(\lambda_ns),S_n(\mu\int_0^sQ_n(u)\,du):0\le s\le t\big)$ augmented by the null sets, with predictable quadratic variations
--   $$
--   \langle M_{n,1}\rangle(t)=\frac{\lambda_nt}{n},\qquad \langle M_{n,2}\rangle(t)=\frac{\mu}{n}\int_0^tQ_n(s)\,ds , \tag{33}
--   $$
--   and $E[\langle M_{n,2}\rangle(t)]<\infty$ for all $t\ge0$.
--
--   The representation (32) is the integral equation to which the continuous map of Theorem 4.1 is applied.
--
--   **Formalization Note** The optional quadratic variations $[M_{n,i}]$ (last sentence of the theorem) are not formalized. Each system has its own Poisson processes $A_n,S_n$; the paper's single pair is a special case.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 215, Theorem 3.4, (32)–(33)

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

/-- **Theorem 3.4** (first martingale representation for the scaled processes, p. 215),
predictable part. For the `M/M/∞` systems of Theorem 1.1 with `E[Qₙ(0)] < ∞` for each `n ≥ 1`,
and each `n ≥ 1`:
1. almost surely, for all `t ≥ 0`, (32) holds:
   `Xₙ(t) = Xₙ(0) + M_{n,1}(t) − M_{n,2}(t) − μ ∫₀ᵗ Xₙ(s) ds`;
2. `M_{n,1}` and `M_{n,2}` of (29)–(30) are square-integrable martingales with respect to the
   augmented filtration `𝓕ₙ,ₜ = σ(Qₙ(0), Aₙ(λₙs), Sₙ(μ ∫₀ˢ Qₙ(u) du) : 0 ≤ s ≤ t) ∨ 𝒩`, with
   predictable quadratic variations `⟨M_{n,1}⟩(t) = λₙt/n` and
   `⟨M_{n,2}⟩(t) = (μ/n) ∫₀ᵗ Qₙ(s) ds` (33), the latter with finite mean. -/
theorem theorem_3_4 (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (hmom : ∀ n : ℕ, 1 ≤ n → Integrable (fun ω => (Q n ω 0 : ℝ)) P) :
    ∀ n : ℕ, 1 ≤ n →
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
        scaled n (Q n) ω t 0 = scaled n (Q n) ω 0 0 + scaledM1 n (n * μ) (A n) ω t
          - scaledM2 n μ (S n) (Q n) ω t - μ * ∫ s in (0 : ℝ)..t, scaled n (Q n) ω s 0) ∧
      IsPQV (historyFiltration P (n * μ) μ (A n) (S n) (Q n)) P
        (fun (t : ℝ≥0) ω => scaledM1 n (n * μ) (A n) ω t)
        (fun (t : ℝ≥0) (_ : Ω) => (n : ℝ) * μ * (t : ℝ) / n) ∧
      IsPQV (historyFiltration P (n * μ) μ (A n) (S n) (Q n)) P
        (fun (t : ℝ≥0) ω => scaledM2 n μ (S n) (Q n) ω t)
        (fun (t : ℝ≥0) ω => phiS n μ (Q n) ω t) := by sorry

end MartingaleHT.InfiniteServer
