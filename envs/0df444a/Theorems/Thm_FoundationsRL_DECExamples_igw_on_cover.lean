-- Prove2me | Theorems.Thm_FoundationsRL_DECExamples_igw_on_cover
-- name    : FoundationsRL.DECExamples.igw_on_cover
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:20:48.794423+00:00
-- url     : https://prove2.me/theorems/cb5ecb0d-d253-4493-a705-89dcc71a3222
-- title:
--   Proof of Proposition 18, second display — Proposition 9 on the cover
-- statement:
--   Let $(\Pi,\rho)$ be a metric space, $\Pi'\subseteq\Pi$ finite, $\widehat f:\Pi\to\mathbb R$, $\gamma\ge1$, and let $p$ be inverse gap weighting (3.36) with parameter $\gamma$ applied to $\widehat f$ and restricted to $\Pi'$. For every $1$-Lipschitz $f:\Pi\to[0,1]$ and every $\pi_0\in\Pi'$,
--
--   $$
--   \mathbb E_{\pi\sim p}[f(\pi_0)-f(\pi)]\le\frac{|\Pi'|}{\gamma}+\gamma\cdot\mathbb E_{\pi\sim p}\Big[\big(f(\pi)-\widehat f(\pi)\big)^2\Big].
--   $$
--
--   The notes apply this at $\pi_0=\iota(\pi_f)$, the cover point next to the maximizer of $f$; it is Proposition 9 on the finite decision space $\Pi'$.
--
--   **Formalization Note** Distributions are `PMF`; $p$ vanishes outside $\Pi'$.
--
--   Differences from the source:
--   - generalization: at π₀ = ι(π_f) → at every π₀ ∈ Π′; reason: ι(π_f) ∈ Π′, so the display is the instance π₀ = ι(π_f)
--   - generalization: Π′ the ε-cover → any finite Π′ ⊆ Π; reason: Proposition 9 needs only a finite decision space; a cover witness is a finite subset
--   - generalization: f̂ : Π → [0, 1] → f̂ : Π → ℝ; reason: Proposition 9 allows any vector f̂; [0, 1]-valued functions are real-valued
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 18, second display, p. 74

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_expect
import Definitions.Def_FoundationsRL_DECExamples_lipschitzClass
import Definitions.Def_FoundationsRL_DECExamples_IsIGWOn

namespace FoundationsRL.DECExamples

/-- **Proof of Proposition 18, second display: Proposition 9 on the cover.** If `p` is inverse gap
weighting over `D'` and `π₀ ∈ D'`, then
`E_{π∼p}[f(π₀) − f(π)] ≤ |D'| / γ + γ · E_{π∼p}[(f(π) − f̂(π))²]`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 18, p. 74.

**Formalization Note.** The notes apply this at `π₀ = ι(π_f)`. -/
theorem igw_on_cover {D : Type*} [MetricSpace D] (D' : Finset D) (fhat : D → ℝ) (γ : ℝ)
    (hγ : 1 ≤ γ) (p : PMF D) (hp : IsIGWOn D' fhat γ p) (f : D → ℝ) (hf : f ∈ lipschitzClass D)
    (π₀ : D) (hπ₀ : π₀ ∈ D') :
    expect p (fun π => f π₀ - f π) ≤
      (D'.card : ℝ) / γ + γ * expect p (fun π => (f π - fhat π) ^ 2) := by sorry

end FoundationsRL.DECExamples
