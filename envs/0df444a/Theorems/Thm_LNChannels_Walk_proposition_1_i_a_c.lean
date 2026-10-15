-- Prove2me | Theorems.Thm_LNChannels_Walk_proposition_1_i_a_c
-- name    : LNChannels.Walk.proposition_1_i_a_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:17.78845+00:00
-- url     : https://prove2.me/theorems/e872f6b0-461a-4ddf-9bc0-46a8bfdd5aa0
-- title:
--   Proposition 1 (i)(a),(c), p. 8 — probability that node 2 exhausts the channel before node 1
-- statement:
--   Let $l_1,l_2\ge1$ be the channel sizes. Start the balance at $0$ and let it perform the walk absorbed at $-l_1$ and $l_2$: steps $+1$ with probability $\lambda_2/(\lambda_1+\lambda_2)$ and $-1$ with probability $\lambda_1/(\lambda_1+\lambda_2)$. Let $\mathbb P_0\{\tau_{l_2}<\tau_{-l_1}\}$ be the probability that the walk reaches $l_2$ (node 2 exhausts the channel) before $-l_1$ (node 1 exhausts it).
--
--   1. (a) If $\lambda_2>\lambda_1>0$ and $q=\lambda_2/\lambda_1$, then
--   $$
--   \mathbb P_0\{\tau_{l_2}<\tau_{-l_1}\}=\frac{1-q^{-l_1}}{1-q^{-l_1-l_2}}.
--   $$
--   2. (c) If $\lambda_2>\lambda_1=0$, then $\mathbb P_0\{\tau_{l_2}<\tau_{-l_1}\}=1$.
--
--   This is the probability that the payee side of the channel is exhausted first.
--
--   **Formalization Note** The probability is the platform's `MarkovMixing.hitBeforeProb`, a series of first-passage probabilities with the convention that a non-summable series sums to $0$. The absorbed walk is absorbed almost surely, so the series converges. Case (b) of the paper, "1/2 if $\lambda_2=\lambda_1>0$", is false unless $l_1=l_2$, and its own proof gives $l_1/(l_1+l_2)$. Case (b) is therefore not posed here. The corrected (b) is the platform theorem `MarkovMixing.gamblers_ruin` with $n=l_1+l_2$ and $k=l_1$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 8 (PDF 9), Proposition 1 (i)(a),(c); proof p. 13 (PDF 14)

import Mathlib
import Definitions.Def_mm_path
import Definitions.Def_LNChannels_Walk_AbsorbedWalk

namespace LNChannels.Walk

/-- Proposition 1 (i), cases (a) and (c), p. 8: started from the balance `0`, the absorbed walk
reaches `+l₂` (node 2 exhausts the channel) before `−l₁` with probability
(a) `(1 − q^{−l₁})/(1 − q^{−l₁−l₂})`, `q = λ₂/λ₁`, if `λ₂ > λ₁ > 0`; (c) `1` if `λ₂ > λ₁ = 0`. -/
theorem proposition_1_i_a_c (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    (0 < lam₁ → lam₁ < lam₂ → ∀ q : ℝ, q = lam₂ / lam₁ →
      MarkovMixing.hitBeforeProb (absorbedWalk lam₁ lam₂ l₁ l₂) (absorbedStart l₁ l₂)
          (Fin.last (l₁ + l₂)) 0 =
        (1 - q ^ (-(l₁ : ℤ))) / (1 - q ^ (-((l₁ + l₂ : ℕ) : ℤ)))) ∧
    (lam₁ = 0 → 0 < lam₂ →
      MarkovMixing.hitBeforeProb (absorbedWalk lam₁ lam₂ l₁ l₂) (absorbedStart l₁ l₂)
          (Fin.last (l₁ + l₂)) 0 = 1) := by sorry

end LNChannels.Walk
