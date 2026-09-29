-- Prove2me | Theorems.Thm_FoundationsRL_Structured_dec_linear_bandits_bound
-- name    : FoundationsRL.Structured.dec_linear_bandits_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:18:52.760986+00:00
-- url     : https://prove2.me/theorems/8df99ea2-c345-4770-8977-6ff51bb94ef7
-- title:
--   Proposition 17 — DEC for Linear Bandits
-- statement:
--   This theorem formalizes **Proposition 17** (Foster & Rakhlin, *Foundations of
--   Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 71): for
--   the linear bandit setting, with a finite decision space `Fin n`, a feature map $\phi :
--   \Pi \to B_2^d(1)$ valued in the closed unit ball, and a parameter set $\Theta \subseteq
--   B_2^d(1)$ giving the function class $F = \{\pi \mapsto \langle\theta,\phi(\pi)\rangle \mid
--   \theta \in \Theta\}$, combining the G-optimal design (Proposition 16) with inverse gap
--   weighting certifies
--
--   $$
--   \mathrm{dec}_\gamma(F) \lesssim \frac{d}{\gamma}.
--   $$
--
--   The book's own proof (pp. 71-72) derives this by summing three terms — an exploration-bias
--   term $(I) \le d/\gamma$, an on-policy estimation term whose $\gamma \cdot
--   \mathbb{E}[(\hat f - f)^2]$ part cancels against the DEC's own $-\gamma(f(\pi) - \hat
--   f(\pi))^2$ subtraction leaving $1/(2\gamma)$, and an at-optimum estimation term $(IV) \le
--   d/\gamma$ — yielding the explicit constant $\mathrm{dec}_\gamma(F) \le (4d+1)/(2\gamma)$,
--   which is the constant this theorem states.
--
--   **Formalization Note** The book writes $\lesssim$; the proof's own derived constant
--   $(4d+1)/(2\gamma)$ replaces it here, per this series' convention of pinning every $\lesssim$
--   to the constant the book's own proof produces, never a weaker or looser one.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 71, Proposition 17

import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC

namespace FoundationsRL.Structured

/-- Proposition 17 (DEC for Linear Bandits) (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 71): consider the linear
bandit setting (p. 70) on a finite decision space `Fin n`, with feature map `phi : Fin n → (Fin
d → ℝ)` valued in the closed unit ball `B₂^d(1)` and parameter set `Θ ⊆ B₂^d(1)`, giving the
function class `F = {π ↦ ⟨θ, φ(π)⟩ | θ ∈ Θ}`. Combining the G-optimal design (Proposition 16)
with inverse gap weighting, the strategy the book constructs certifies `decγ(F) ≲ d/γ`; the
proof (p. 71–72) derives the explicit constant `decγ(F) ≤ (4d+1)/(2γ)` by summing the
exploration-bias term `(I) ≤ d/γ`, the on-policy estimation term whose `γ·E[(f̂−f)²]` part
cancels against the DEC's own `−γ(f(π)−f̂(π))²` subtraction leaving `1/(2γ)`, and the
at-optimum estimation term `(IV) ≤ d/γ`. -/
theorem dec_linear_bandits_bound {n d : ℕ} (hd : 0 < d)
    (phi : Fin n → Fin d → ℝ) (hphi : ∀ i, ∑ k, (phi i k) ^ 2 ≤ 1)
    (Θ : Set (Fin d → ℝ)) (hΘ : ∀ θ ∈ Θ, ∑ k, (θ k) ^ 2 ≤ 1)
    (piStar : (Fin n → ℝ) → Fin n)
    (hpiStar : ∀ f ∈ {f : Fin n → ℝ | ∃ θ ∈ Θ, ∀ i, f i = ∑ k, θ k * phi i k},
      ∀ π, f π ≤ f (piStar f))
    (γ : ℝ) (hγ : 0 < γ) :
    dec {f : Fin n → ℝ | ∃ θ ∈ Θ, ∀ i, f i = ∑ k, θ k * phi i k} piStar γ
      ≤ (4 * (d : ℝ) + 1) / (2 * γ) := by sorry

end FoundationsRL.Structured
